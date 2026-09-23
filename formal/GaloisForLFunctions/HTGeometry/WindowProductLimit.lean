import GaloisForLFunctions.HTGeometry.LinearSecondOrderLimit

/-!
# Pairings pass to a uniform limit on a window

If two families converge uniformly on a window and one of them stays bounded there, their pairing
converges to the pairing of the limits: the defect splits as

`fg − vw = f(g − w) + (f − v)w` ,

so it is at most `E(B + C)` pointwise, and integrating over the window costs only its length.

This is what lets orthogonality of a family of profiles pass to the limit profiles.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Uniform product estimate on a window.** -/
theorem abs_intervalIntegral_product_sub_le {f g v w : ℝ → ℝ} {a b E B C : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (uIcc a b)) (hgc : ContinuousOn g (uIcc a b))
    (hvc : ContinuousOn v (uIcc a b)) (hwc : ContinuousOn w (uIcc a b))
    (hfv : ∀ x ∈ Icc a b, |f x - v x| ≤ E) (hgw : ∀ x ∈ Icc a b, |g x - w x| ≤ E)
    (hfb : ∀ x ∈ Icc a b, |f x| ≤ B) (hwb : ∀ x ∈ Icc a b, |w x| ≤ C)
    (hE : 0 ≤ E) (hB : 0 ≤ B) :
    |(∫ x in a..b, f x * g x) - ∫ x in a..b, v x * w x| ≤ (E * (B + C)) * (b - a) := by
  refine abs_intervalIntegral_sub_le_of_uniform hab (hfc.mul hgc) (hvc.mul hwc) ?_
  intro x hx
  have hsplit : f x * g x - v x * w x = f x * (g x - w x) + (f x - v x) * w x := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul]
  have h1 : |f x| * |g x - w x| ≤ B * E :=
    mul_le_mul (hfb x hx) (hgw x hx) (abs_nonneg _) hB
  have h2 : |f x - v x| * |w x| ≤ E * C :=
    mul_le_mul (hfv x hx) (hwb x hx) (abs_nonneg _) hE
  nlinarith [h1, h2]

/-- **Pairings converge.**  A family whose members converge uniformly on a window, with one factor
uniformly bounded, has pairings converging to the pairing of the limits. -/
theorem tendsto_intervalIntegral_product {ι : Type*} {L : Filter ι}
    {f g : ι → ℝ → ℝ} {v w : ℝ → ℝ} {a b B C : ℝ} {E : ι → ℝ} (hab : a ≤ b)
    (hfc : ∀ i, ContinuousOn (f i) (uIcc a b)) (hgc : ∀ i, ContinuousOn (g i) (uIcc a b))
    (hvc : ContinuousOn v (uIcc a b)) (hwc : ContinuousOn w (uIcc a b))
    (hfv : ∀ i, ∀ x ∈ Icc a b, |f i x - v x| ≤ E i)
    (hgw : ∀ i, ∀ x ∈ Icc a b, |g i x - w x| ≤ E i)
    (hfb : ∀ i, ∀ x ∈ Icc a b, |f i x| ≤ B) (hwb : ∀ x ∈ Icc a b, |w x| ≤ C)
    (hEnn : ∀ i, 0 ≤ E i) (hB : 0 ≤ B) (hE : Tendsto E L (𝓝 0)) :
    Tendsto (fun i => ∫ x in a..b, f i x * g i x) L (𝓝 (∫ x in a..b, v x * w x)) := by
  have henv : Tendsto (fun i => (E i * (B + C)) * (b - a)) L (𝓝 0) := by
    have h1 := (hE.mul_const (B + C)).mul_const (b - a)
    simpa using h1
  have hbnd : ∀ i, ‖(∫ x in a..b, f i x * g i x) - ∫ x in a..b, v x * w x‖
      ≤ (E i * (B + C)) * (b - a) := by
    intro i
    simpa [Real.norm_eq_abs] using
      abs_intervalIntegral_product_sub_le hab (hfc i) (hgc i) hvc hwc (hfv i) (hgw i)
        (hfb i) hwb (hEnn i) hB
  have hzero := squeeze_zero_norm' (Filter.Eventually.of_forall hbnd) henv
  have := hzero.add_const (∫ x in a..b, v x * w x)
  simpa using this

/-- **Pairings converge, under eventual hypotheses.**  Only the eventual behaviour of the family
along the filter matters, which is the form a bandwidth-indexed family supplies. -/
theorem tendsto_intervalIntegral_product_eventually {ι : Type*} {L : Filter ι}
    {f g : ι → ℝ → ℝ} {v w : ℝ → ℝ} {a b B C : ℝ} {E : ι → ℝ} (hab : a ≤ b)
    (hvc : ContinuousOn v (uIcc a b)) (hwc : ContinuousOn w (uIcc a b))
    (hwb : ∀ x ∈ Icc a b, |w x| ≤ C) (hB : 0 ≤ B)
    (hev : ∀ᶠ i in L, ContinuousOn (f i) (uIcc a b) ∧ ContinuousOn (g i) (uIcc a b) ∧
      (∀ x ∈ Icc a b, |f i x - v x| ≤ E i) ∧ (∀ x ∈ Icc a b, |g i x - w x| ≤ E i) ∧
      (∀ x ∈ Icc a b, |f i x| ≤ B) ∧ 0 ≤ E i)
    (hE : Tendsto E L (𝓝 0)) :
    Tendsto (fun i => ∫ x in a..b, f i x * g i x) L (𝓝 (∫ x in a..b, v x * w x)) := by
  have henv : Tendsto (fun i => (E i * (B + C)) * (b - a)) L (𝓝 0) := by
    have h1 := (hE.mul_const (B + C)).mul_const (b - a)
    simpa using h1
  have hbnd : ∀ᶠ i in L, ‖(∫ x in a..b, f i x * g i x) - ∫ x in a..b, v x * w x‖
      ≤ (E i * (B + C)) * (b - a) := by
    filter_upwards [hev] with i hi
    obtain ⟨hfc, hgc, hfv, hgw, hfb, hEnn⟩ := hi
    simpa [Real.norm_eq_abs] using
      abs_intervalIntegral_product_sub_le hab hfc hgc hvc hwc hfv hgw hfb hwb hEnn hB
  have hzero := squeeze_zero_norm' hbnd henv
  have := hzero.add_const (∫ x in a..b, v x * w x)
  simpa using this

/-- **Two families cannot converge to the same nonzero profile while staying orthogonal.**  If the
window pairings of two families converge to the window mass of a common limit profile, while
approximate orthogonality forces those pairings to be `O(K⁻²)`, the limit profile has vanishing
window mass — contradicting positivity. -/
theorem false_of_orthogonal_same_limit {ι : Type*} {L : Filter ι} [L.NeBot] {C : ℝ}
    {f g : ι → ℝ → ℝ} {v : ℝ → ℝ}
    (hconv : ∀ K : ℝ, 0 < K → Tendsto (fun i => ∫ x in (-K)..K, f i x * g i x) L
      (𝓝 (∫ x in (-K)..K, v x * v x)))
    (horth : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, |∫ x in (-K)..K, f i x * g i x| ≤ C / K ^ (2 : ℕ))
    (hvpos : 0 < ∫ x in (-1 : ℝ)..1, v x * v x)
    (hmono : ∀ K : ℝ, 1 ≤ K →
      (∫ x in (-1 : ℝ)..1, v x * v x) ≤ ∫ x in (-K)..K, v x * v x) :
    False := by
  set δ : ℝ := ∫ x in (-1 : ℝ)..1, v x * v x with hδ
  -- every window mass of the limit profile is at most `C/K²`
  have hbound : ∀ K : ℝ, 0 < K → (∫ x in (-K)..K, v x * v x) ≤ C / K ^ (2 : ℕ) := by
    intro K hKpos
    refine le_of_tendsto (hconv K hKpos) ?_
    filter_upwards [horth K hKpos] with i hi
    exact le_trans (le_abs_self _) hi
  -- so `δ ≤ C/K²` for every `K ≥ 1`
  have hδle : ∀ K : ℝ, 1 ≤ K → δ ≤ C / K ^ (2 : ℕ) := fun K hK =>
    le_trans (hmono K hK) (hbound K (lt_of_lt_of_le one_pos hK))
  -- but `C/K² → 0`
  have hCzero : Tendsto (fun K : ℝ => C / K ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun K : ℝ => K ^ (2 : ℕ)) atTop atTop :=
      tendsto_pow_atTop (n := 2) (Nat.succ_ne_zero 1)
    exact tendsto_const_nhds.div_atTop hsq
  obtain ⟨K, hK1, hKlt⟩ : ∃ K : ℝ, 1 ≤ K ∧ C / K ^ (2 : ℕ) < δ := by
    obtain ⟨K, hKa, hKb⟩ :=
      ((hCzero.eventually (eventually_lt_nhds hvpos)).and (eventually_ge_atTop (1 : ℝ))).exists
    exact ⟨K, hKb, hKa⟩
  exact absurd (hδle K hK1) (not_le.2 hKlt)

end GaloisForLFunctions.HTGeometry
