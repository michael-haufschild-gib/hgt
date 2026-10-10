import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalQuadrature

/-! The complete canonical probability moment fiber is an explicit line segment. -/

open scoped BigOperators
noncomputable section
namespace RHTower

def finiteWeilCanonicalMixture (r k : ℕ) (a : ℝ) (i : Fin (r + 2)) : ℝ :=
  a * finiteWeilCanonicalPositiveProfile r k i +
    (1 - a) * finiteWeilCanonicalNegativeProfile r k i

def finiteWeilCanonicalMomentFiber (r k : ℕ) (v : Fin (r + 2) → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧
    ∀ p ≤ r, (∑ i, v i * finiteWeilClusterLogNodes r k i ^ p) =
      ∑ i, finiteWeilCanonicalPositiveProfile r k i * finiteWeilClusterLogNodes r k i ^ p

private theorem positive_entry_of_sum_one {n : ℕ} (v : Fin n → ℝ)
    (hv : ∑ i, v i = 1) : ∃ i, 0 < v i := by
  by_contra h
  have hn (i : Fin n) : v i ≤ 0 := le_of_not_gt (fun hi => h ⟨i, hi⟩)
  have hs : ∑ i, v i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
  linarith only [hv, hs]

theorem finiteWeilCanonicalMixture_nonneg_iff (r k : ℕ) (a : ℝ) :
    (∀ i, 0 ≤ finiteWeilCanonicalMixture r k a i) ↔ 0 ≤ a ∧ a ≤ 1 := by
  have hs := finiteWeilCanonicalProfiles_spec r k
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := positive_entry_of_sum_one _ hs.2.1
    obtain ⟨j, hj⟩ := positive_entry_of_sum_one _ hs.2.2.1
    have hQi : finiteWeilCanonicalNegativeProfile r k i = 0 :=
      (mul_eq_zero.mp (hs.1 i).2.2.1).resolve_left hi.ne'
    have hPj : finiteWeilCanonicalPositiveProfile r k j = 0 :=
      (mul_eq_zero.mp (hs.1 j).2.2.1).resolve_right hj.ne'
    have hai : 0 ≤ a * finiteWeilCanonicalPositiveProfile r k i := by
      simpa only [finiteWeilCanonicalMixture, hQi, mul_zero, add_zero] using ha i
    have haj : 0 ≤ (1 - a) * finiteWeilCanonicalNegativeProfile r k j := by
      simpa only [finiteWeilCanonicalMixture, hPj, mul_zero, zero_add] using ha j
    refine ⟨nonneg_of_mul_nonneg_right (by simpa only [mul_comm] using hai) hi, ?_⟩
    have := nonneg_of_mul_nonneg_right (by simpa only [mul_comm] using haj) hj
    linarith
  · rintro ⟨ha, ha1⟩ i
    exact add_nonneg (mul_nonneg ha (hs.1 i).1)
      (mul_nonneg (sub_nonneg.mpr ha1) (hs.1 i).2.1)

theorem finiteWeilCanonicalMixture_injective (r k : ℕ) :
    Function.Injective (finiteWeilCanonicalMixture r k) := by
  have hs := finiteWeilCanonicalProfiles_spec r k
  obtain ⟨i, hi⟩ := positive_entry_of_sum_one _ hs.2.1
  have hQi : finiteWeilCanonicalNegativeProfile r k i = 0 :=
    (mul_eq_zero.mp (hs.1 i).2.2.1).resolve_left hi.ne'
  intro a b hab
  have he := congrFun hab i
  simp only [finiteWeilCanonicalMixture, hQi, mul_zero, add_zero] at he
  exact mul_right_cancel₀ hi.ne' he

theorem finiteWeilCanonicalMixture_mem (r k : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteWeilCanonicalMomentFiber r k (finiteWeilCanonicalMixture r k a) := by
  have hs := finiteWeilCanonicalProfiles_spec r k
  refine ⟨(finiteWeilCanonicalMixture_nonneg_iff r k a).mpr ⟨ha, ha1⟩, ?_, ?_⟩
  · simp only [finiteWeilCanonicalMixture, Finset.sum_add_distrib, ← Finset.mul_sum,
      hs.2.1, hs.2.2.1, mul_one]
    ring
  · intro p hp
    simp only [finiteWeilCanonicalMixture, add_mul, mul_assoc, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [← hs.2.2.2.2.1 p hp]
    ring

/-- No other direction survives the first `r+1` moment constraints. -/
theorem finiteWeilCanonicalProfiles_annihilator_span (r k : ℕ) (c : Fin (r + 2) → ℝ)
    (hm : ∀ p ≤ r, ∑ i, c i * finiteWeilClusterLogNodes r k i ^ p = 0) :
    ∃ a : ℝ, ∀ i, c i = a *
      (finiteWeilCanonicalPositiveProfile r k i - finiteWeilCanonicalNegativeProfile r k i) := by
  let W := finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)
  let A := ∑ i, c i * finiteWeilClusterLogNodes r k i ^ (r + 1)
  let t := (2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) * ‖W‖⁻¹
  have hW : 0 < ‖W‖ :=
    finiteWeilMomentWeights_norm_pos _ (finiteWeilClusterLogNodes_injective r k)
  have ht : 0 < t := mul_pos
    (finiteWeil_profile_scale_bounds _ (finiteWeilCanonicalCluster_spec r k).1
      (finiteWeilCanonicalCluster_sum_zero r k)).1 (inv_pos.mpr hW)
  have hc : c = A • W := finiteWeilMomentWeights_span _
    (finiteWeilClusterLogNodes_injective r k) c (fun p hp => hm p (by omega))
  have hd (i : Fin (r + 2)) :
      finiteWeilCanonicalPositiveProfile r k i - finiteWeilCanonicalNegativeProfile r k i =
        t * W i := by
    unfold finiteWeilCanonicalPositiveProfile finiteWeilCanonicalNegativeProfile
    rw [finiteWeil_profile_difference]
    change (2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
      (‖W‖⁻¹ * W i) = t * W i
    dsimp [t]
    ring
  refine ⟨A / t, fun i => ?_⟩
  rw [hd]
  calc
    c i = A * W i := congrFun hc i
    _ = (A / t) * (t * W i) := by rw [← mul_assoc, div_mul_cancel₀ _ ht.ne']

/-- Every probability with these moments is a unique mixture of the two endpoints. -/
theorem finiteWeilCanonicalMomentFiber_iff (r k : ℕ) (v : Fin (r + 2) → ℝ) :
    finiteWeilCanonicalMomentFiber r k v ↔
      ∃! a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ v = finiteWeilCanonicalMixture r k a := by
  constructor
  · intro hv
    have hs := finiteWeilCanonicalProfiles_spec r k
    have hm (p : ℕ) (hp : p ≤ r) :
        ∑ i, (v i - finiteWeilCanonicalNegativeProfile r k i) *
          finiteWeilClusterLogNodes r k i ^ p = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [hv.2.2 p hp, hs.2.2.2.2.1 p hp, sub_self]
    obtain ⟨a, ha⟩ := finiteWeilCanonicalProfiles_annihilator_span r k
      (fun i => v i - finiteWeilCanonicalNegativeProfile r k i) hm
    have he : v = finiteWeilCanonicalMixture r k a := by
      funext i
      have hi := ha i
      dsimp [finiteWeilCanonicalMixture]
      linarith only [hi]
    have hbounds := (finiteWeilCanonicalMixture_nonneg_iff r k a).mp (he ▸ hv.1)
    refine ⟨a, ⟨hbounds.1, hbounds.2, he⟩, ?_⟩
    intro b hb
    exact finiteWeilCanonicalMixture_injective r k (hb.2.2.symm.trans he)
  · rintro ⟨a, ha, _⟩
    rw [ha.2.2]
    exact finiteWeilCanonicalMixture_mem r k a ha.1 ha.2.1

theorem finiteWeilCanonicalMixture_difference (r k : ℕ) (a b : ℝ) (i : Fin (r + 2)) :
    finiteWeilCanonicalMixture r k a i - finiteWeilCanonicalMixture r k b i =
      (a - b) * (finiteWeilCanonicalPositiveProfile r k i -
        finiteWeilCanonicalNegativeProfile r k i) := by
  unfold finiteWeilCanonicalMixture
  ring

/-- The mixture coordinate scales absolute distance by exactly two. -/
theorem finiteWeilCanonicalMixture_abs_distance (r k : ℕ) (a b : ℝ) :
    (∑ i, |finiteWeilCanonicalMixture r k a i - finiteWeilCanonicalMixture r k b i|) =
      2 * |a - b| := by
  simp only [finiteWeilCanonicalMixture_difference, abs_mul, ← Finset.mul_sum]
  rw [(finiteWeilCanonicalProfiles_spec r k).2.2.2.1, mul_comm]

end RHTower
