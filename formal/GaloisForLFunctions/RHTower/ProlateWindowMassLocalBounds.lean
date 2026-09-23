import GaloisForLFunctions.RHTower.ProlateWindowMassLimit

/-!
# Window-local phase bounds in the prolate counting argument

The compact-window ODE method supplies a bound depending on window radius, not one bound on the
whole real line.  These strengthenings of the prolate-to-oscillator counting theorems accept the
mathematically natural family `B K`; no proof of the counting conclusion uses uniformity in `K`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A window-dependent phase bound still forces every integrable limit onto an even oscillator
rung. -/
theorem exists_evenRung_of_prolate_family_windowBound
    {ι : Type*} {L : Filter ι} [L.NeBot]
    {mu c : ι → ℝ} {B : ℝ → ℝ} {N m : ℝ} {u u' u'' : ι → ℝ → ℝ}
    (hB : ∀ K, 0 < K → 0 ≤ B K)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x)
    (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (heu : ∀ i, Function.Even (u i))
    (hev : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ (2 : ℕ) ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B K) ∧
      u i 0 = 1 ∧ u' i 0 = 0)
    (hmass : ∀ K : ℝ, 0 < K → ∀ᶠ i in L,
      (∫ x in (-K)..K, u i x * u i x) ≤ N)
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    ∃ n : ℕ, Even n ∧ m = 2 * (n : ℝ) + 1 := by
  have hconv : ∀ K : ℝ, 0 < K →
      Tendsto (fun i => ∫ x in (-K)..K, u i x * u i x) L
        (𝓝 (∫ x in (-K)..K, oscProfile m x * oscProfile m x)) :=
    fun K hK => tendsto_prolateWindowMass hK (hB K hK) hu hu' heu (hev K hK) hmu hc
  exact even_rung_of_integrable_oscProfile
    (integrable_sq_of_bounded_window_limits (continuous_oscProfile m) hconv hmass)

/-- Orthogonal prolate families with window-dependent phase bounds cannot coalesce at one limiting
oscillator profile. -/
theorem prolateFamily_limit_ne_windowBound
    {ι : Type*} {L : Filter ι} [L.NeBot]
    {mu nu c : ι → ℝ} {B : ℝ → ℝ} {C m m' : ℝ}
    {u u' u'' v v' v'' : ι → ℝ → ℝ}
    (hB : ∀ K, 0 < K → 0 ≤ B K)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x)
    (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hv : ∀ i x, HasDerivAt (v i) (v' i x) x)
    (hv' : ∀ i x, HasDerivAt (v' i) (v'' i x) x)
    (heu : ∀ i, Function.Even (u i)) (hevn : ∀ i, Function.Even (v i))
    (hevu : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ (2 : ℕ) ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B K) ∧
      u i 0 = 1 ∧ u' i 0 = 0)
    (hevv : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, 2 * K ^ (2 : ℕ) ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, v'' i x = rescaledProlateP (c i) (nu i) x * v i x
        + rescaledProlateQ (c i) x * v' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |v i x| |v' i x| ≤ B K) ∧
      v i 0 = 1 ∧ v' i 0 = 0)
    (hpair : ∀ K : ℝ, 0 < K → ∀ᶠ i in L,
      |∫ x in (-K)..K, u i x * v i x| ≤ C / K ^ (2 : ℕ))
    (hmu : Tendsto mu L (𝓝 m)) (hnu : Tendsto nu L (𝓝 m'))
    (hc : Tendsto c L atTop) : m ≠ m' := by
  intro heq
  subst heq
  refine false_of_orthogonal_same_limit (C := C) (v := oscProfile m) ?_ hpair
    (integral_oscProfile_mul_self_pos m one_pos)
    (fun K hK => integral_oscProfile_mul_self_mono m hK)
  intro K hK
  exact tendsto_prolateWindowPairing hK (hB K hK) hu hu' hv hv' heu hevn
    (hevu K hK) (hevv K hK) hmu hnu hc

/-- Counting contradiction with the correct window-local phase hypothesis. -/
theorem false_of_orthogonal_prolateFamily_below_windowBound
    {j : ℕ} {ι : Type*} {L : Filter ι} [L.NeBot]
    {c : ι → ℝ} {mu : Fin (j + 1) → ι → ℝ} {m : Fin (j + 1) → ℝ}
    {B : ℝ → ℝ} {N C : ℝ} {u u' u'' : Fin (j + 1) → ι → ℝ → ℝ}
    (hB : ∀ K, 0 < K → 0 ≤ B K)
    (hu : ∀ k i x, HasDerivAt (u k i) (u' k i x) x)
    (hu' : ∀ k i x, HasDerivAt (u' k i) (u'' k i x) x)
    (heu : ∀ k i, Function.Even (u k i))
    (hev : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ i in L,
      0 < c i ∧ 2 * K ^ (2 : ℕ) ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' k i x = rescaledProlateP (c i) (mu k i) x * u k i x
        + rescaledProlateQ (c i) x * u' k i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u k i x| |u' k i x| ≤ B K) ∧
      u k i 0 = 1 ∧ u' k i 0 = 0)
    (hmass : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ i in L,
      (∫ x in (-K)..K, u k i x * u k i x) ≤ N)
    (hpair : ∀ k l : Fin (j + 1), k ≠ l → ∀ K : ℝ, 0 < K → ∀ᶠ i in L,
      |∫ x in (-K)..K, u k i x * u l i x| ≤ C / K ^ (2 : ℕ))
    (hmu : ∀ k, Tendsto (mu k) L (𝓝 (m k))) (hc : Tendsto c L atTop)
    (hbelow : ∀ k, m k < 4 * (j : ℝ) + 1) : False := by
  have hdistinct : Function.Injective m := by
    intro k l hkl
    by_contra hne
    refine prolateFamily_limit_ne_windowBound (C := C) hB
      (hu k) (hu' k) (hu l) (hu' l) (heu k) (heu l)
      (hev k) (fun K hK => (hev l K hK).mono fun i hi =>
        ⟨hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2⟩)
      (hpair k l hne) (hmu k) (hmu l) hc hkl
  refine not_injective_evenRung_below m (fun k => ?_) hbelow hdistinct
  obtain ⟨n, hne, hm⟩ := exists_evenRung_of_prolate_family_windowBound hB
    (hu k) (hu' k) (heu k) (hev k) (hmass k) (hmu k) hc
  exact ⟨n, hne, hm⟩

end RHTower
