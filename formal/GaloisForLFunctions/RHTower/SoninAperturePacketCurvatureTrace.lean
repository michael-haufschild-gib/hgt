import GaloisForLFunctions.RHTower.SoninApertureCurvatureTrace

/-!
# Aperture curvature of a finite source packet

A single prime scale contributes an aperture curvature whose real trace is minus the coupling
energy between the two successive lost layers.  An actual finite source packet is a weighted family
of prime scales, and its curvature is the corresponding weighted sum.

Because the concrete relative ideal is closed under finite sums and scalar multiples, the packet
curvature is again Schatten-1, its ordinary trace is the weighted sum of the individual traces, and
for nonnegative weights its real trace is nonpositive: no reweighting of a finite packet can turn
the aperture curvature positive.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The concrete relative ideal is closed under finite sums. -/
theorem IsSoninPrincipalRelativeIdeal.sum {ι : Type*} (s : Finset ι)
    (T : ι → evenSubspace →L[Complex] evenSubspace)
    (h : ∀ i ∈ s, IsSoninPrincipalRelativeIdeal (T i)) :
    IsSoninPrincipalRelativeIdeal (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using IsSoninPrincipalRelativeIdeal.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The ordinary trace is additive over a finite family of relative-ideal corrections. -/
theorem opTrace_sum_of_isSoninPrincipalRelativeIdeal {ι : Type*} (s : Finset ι)
    (T : ι → evenSubspace →L[Complex] evenSubspace)
    (h : ∀ i ∈ s, IsSoninPrincipalRelativeIdeal (T i)) :
    opTrace (∑ i ∈ s, T i) = ∑ i ∈ s, opTrace (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have hrest : IsSoninPrincipalRelativeIdeal (∑ j ∈ s, T j) :=
        IsSoninPrincipalRelativeIdeal.sum s T
          (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        opTrace_add_of_memSchattenClass_one
          (h i (Finset.mem_insert_self i s)).memSchattenClass_one
          hrest.memSchattenClass_one,
        ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

/-- Aperture curvature of a finite weighted packet of prime scales. -/
def soninAperturePacketCurvature {ι : Type*} (s : Finset ι) (a b c : ℝ)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (w : ι → ℝ) :
    evenSubspace →L[Complex] evenSubspace :=
  ∑ i ∈ s, ((w i : ℝ) : Complex) •
    evenSoninApertureRestrictionCurvature a b c (p i) (hp i)

/-- The packet curvature stays inside the concrete relative ideal. -/
theorem soninAperturePacketCurvature_mem_principalRelativeIdeal
    {ι : Type*} (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (w : ι → ℝ)
    (hcp : ∀ i ∈ s, c < p i * a) :
    IsSoninPrincipalRelativeIdeal
      (soninAperturePacketCurvature s a b c p hp w) := by
  refine IsSoninPrincipalRelativeIdeal.sum s _ fun i hi => ?_
  exact (evenSoninApertureRestrictionCurvature_mem_principalRelativeIdeal
    ha hab hbc (hp i) (hcp i hi)).smul _

/-- **Packet curvature trace.**  The ordinary trace of the packet curvature is the weighted sum of
the single-scale curvature traces. -/
theorem opTrace_soninAperturePacketCurvature
    {ι : Type*} (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (w : ι → ℝ)
    (hcp : ∀ i ∈ s, c < p i * a) :
    opTrace (soninAperturePacketCurvature s a b c p hp w) =
      ∑ i ∈ s, ((w i : ℝ) : Complex) *
        opTrace (evenSoninApertureRestrictionCurvature a b c (p i) (hp i)) := by
  unfold soninAperturePacketCurvature
  rw [opTrace_sum_of_isSoninPrincipalRelativeIdeal s _ fun i hi =>
    (evenSoninApertureRestrictionCurvature_mem_principalRelativeIdeal
      ha hab hbc (hp i) (hcp i hi)).smul _]
  exact Finset.sum_congr rfl fun i _ => opTrace_smul _ _

/-- **Exact packet energy law.**  The real trace of the aperture curvature of a finite source
packet is minus the weighted total coupling energy between successive lost layers. -/
theorem re_opTrace_soninAperturePacketCurvature
    {ι : Type*} (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (w : ι → ℝ)
    (hcp : ∀ i ∈ s, c < p i * a) :
    (opTrace (soninAperturePacketCurvature s a b c p hp w)).re =
      -∑ i ∈ s, w i * hsNormSq
        (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) := by
  rw [opTrace_soninAperturePacketCurvature s ha hab hbc p hp w hcp, Complex.re_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Complex.re_ofReal_mul,
    re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
      ha hab hbc (hp i) (hcp i hi)]
  ring

/-- **No positive reweighting.**  For nonnegative weights the packet curvature trace is
nonpositive: an actual finite source packet cannot turn the aperture curvature positive, whatever
primes and weights it uses. -/
theorem re_opTrace_soninAperturePacketCurvature_nonpos
    {ι : Type*} (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hcp : ∀ i ∈ s, c < p i * a) :
    (opTrace (soninAperturePacketCurvature s a b c p hp w)).re ≤ 0 := by
  rw [re_opTrace_soninAperturePacketCurvature s ha hab hbc p hp w hcp]
  have hnn : (0 : ℝ) ≤ ∑ i ∈ s, w i * hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hsNormSq_nonneg _)
  linarith

end RHTower
