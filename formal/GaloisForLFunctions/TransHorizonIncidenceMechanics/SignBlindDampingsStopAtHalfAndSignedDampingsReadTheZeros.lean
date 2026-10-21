import GaloisForLFunctions.TransHorizonIncidenceMechanics.UnsignedMajorantsAndSignBlindDataStopAtHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros

/-!
# Sign-blind dampings stop at half; signed dampings read the zeros

Two sets of dampings of the pronic receiver on the damped class `𝒞(K, ε) = {|c(d)| ≤ K d^{−ε}}`.

* `signBlindDampings K`: the dampings at which one budget bounds the receiver of every weight of
  the class, the reading available to magnitudes, amplitudes and unsigned majorants. It is exactly
  `(½, ∞)` (`signBlindDampings_eq_Ioi_half`), with infimum `½` (`sInf_signBlindDampings`) and
  accumulation points `[½, ∞)` (`derivedSet_signBlindDampings`): the sign-blind reading of the
  damping is the trivial rate.
* `receiverDampings`: the dampings at which the signed Möbius weight `μ(d) d^{−ε}` has a bounded
  receiver (`mem_receiverDampings_iff_receiverBounded`). It contains the sign-blind dampings
  (`signBlindDampings_subset_receiverDampings`), and below `½` it reads the zeros: an
  accumulation point `ε₀` of the signed dampings bounds every zero of the strip by `½ + ε₀`
  (`re_le_of_accPt_receiverDampings`), whereas an accumulation point of the sign-blind dampings
  is at least `½` (`half_le_of_accPt_signBlindDampings`).

The sign-blind coarsening of the receiver family has threshold `½`; the signed family passes it,
and what it reads below `½` is the position of the zeros.
-/

open Filter Topology Set
open GaloisForLFunctions.BezoutValuationIncidence
open _root_.RHTower

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The sign-blind dampings -/

/-- The sign-blind dampings: `ε > 0` at which one budget bounds the receiver of every weight of
the damped class `|c(d)| ≤ K d^{−ε}`. -/
def signBlindDampings (K : ℝ) : Set ℝ :=
  {ε : ℝ | 0 < ε ∧ ∃ E : ℝ, ∀ c : ℕ → ℝ, DampedClass K ε c → ∀ T : ℕ,
    weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E}

/-- **The sign-blind dampings are exactly `(½, ∞)`.** -/
theorem signBlindDampings_eq_Ioi_half {K : ℝ} (hK : 0 < K) :
    signBlindDampings K = Ioi (1 / 2) := by
  ext ε
  simp only [signBlindDampings, mem_setOf_eq, mem_Ioi]
  constructor
  · rintro ⟨hε, h⟩
    exact (uniformReceiverBound_iff_half_lt hK hε).mp h
  · intro h
    exact ⟨by linarith, (uniformReceiverBound_iff_half_lt hK (by linarith)).mpr h⟩

/-- The sign-blind reading of the damping is the trivial rate `½`. -/
theorem sInf_signBlindDampings {K : ℝ} (hK : 0 < K) : sInf (signBlindDampings K) = 1 / 2 := by
  rw [signBlindDampings_eq_Ioi_half hK, csInf_Ioi]

/-- An accumulation point of the sign-blind dampings is at least `½`. -/
theorem half_le_of_accPt_signBlindDampings {K : ℝ} (hK : 0 < K) {ε₀ : ℝ}
    (h : AccPt ε₀ (𝓟 (signBlindDampings K))) : 1 / 2 ≤ ε₀ := by
  rw [signBlindDampings_eq_Ioi_half hK] at h
  have := mem_closure_iff_clusterPt.mpr h.clusterPt
  rwa [closure_Ioi] at this

/-- The accumulation points of the sign-blind dampings are exactly `[½, ∞)`. -/
theorem derivedSet_signBlindDampings {K : ℝ} (hK : 0 < K) :
    derivedSet (signBlindDampings K) = Ici (1 / 2) := by
  ext ε₀
  constructor
  · intro h
    exact half_le_of_accPt_signBlindDampings hK (mem_derivedSet.mp h)
  · intro h
    rw [mem_derivedSet, signBlindDampings_eq_Ioi_half hK]
    exact accPt_of_Ioo_subset (lt_add_one ε₀) fun x hx => by
      rw [mem_Ioi]; linarith [hx.1, mem_Ici.mp h]

/-! ### The signed dampings -/

/-- The signed Möbius weight `μ(d) d^{−ε}` lies in the damped class with `K = 1`. -/
theorem dampedClass_one_pmPowerDampedRealWeight (ε : ℝ) :
    DampedClass 1 ε (pmPowerDampedRealWeight ε) := fun d => by
  have hr : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  simp only [pmPowerDampedRealWeight]
  rw [abs_mul, abs_of_nonneg hr, one_mul]
  exact mul_le_of_le_one_left hr (abs_moebiusReal_le_one' d)

/-- Admissibility of a damping is receiver boundedness of the signed Möbius weight, centred at
its mean `1/ζ(1 + ε)`. -/
theorem mem_receiverDampings_iff_receiverBounded {ε : ℝ} (hε : 0 < ε) :
    ε ∈ receiverDampings ↔ ReceiverBounded (pmPowerDampedRealWeight ε) := by
  have hm : (∑' d : ℕ, pmPowerDampedRealWeight ε d / d) = dampedDensity ε :=
    (dampedDensity_eq_tsum hε).symm
  simp only [receiverDampings, mem_setOf_eq, hε, true_and, ReceiverBounded, hm,
    weightPronicEnergy_pmPowerDamped]

/-- Every sign-blind damping is admissible for the signed weight. -/
theorem signBlindDampings_subset_receiverDampings : signBlindDampings 1 ⊆ receiverDampings := by
  rintro ε ⟨hε, E, hE⟩
  rw [mem_receiverDampings_iff_receiverBounded hε]
  exact ⟨E, hE _ (dampedClass_one_pmPowerDampedRealWeight ε)⟩

/-- **Signs read below half damping.** The sign-blind dampings are `(½, ∞)` for every `K > 0`
and their accumulation points are `≥ ½`; the signed dampings contain them together with `[½, ∞)`,
and each of their accumulation points `ε₀` confines every zero of the strip to `Re ρ ≤ ½ + ε₀`. -/
theorem signs_read_below_half_damping :
    (∀ K : ℝ, 0 < K → signBlindDampings K = Ioi (1 / 2)) ∧
    (∀ K : ℝ, 0 < K → ∀ ε₀ : ℝ, AccPt ε₀ (𝓟 (signBlindDampings K)) → 1 / 2 ≤ ε₀) ∧
    signBlindDampings 1 ⊆ receiverDampings ∧ Ici (1 / 2) ⊆ receiverDampings ∧
    (∀ ε₀ : ℝ, AccPt ε₀ (𝓟 receiverDampings) →
      ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re < 1 → ρ.re ≤ 1 / 2 + ε₀) :=
  ⟨fun _ hK => signBlindDampings_eq_Ioi_half hK,
    fun _ hK _ h => half_le_of_accPt_signBlindDampings hK h,
    signBlindDampings_subset_receiverDampings, Ici_half_subset_receiverDampings,
    fun _ h _ hzero hρ1 => re_le_of_accPt_receiverDampings h hzero hρ1⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
