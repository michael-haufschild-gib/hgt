import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCompletedMean
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCoefficientShift
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencySynthesis
open Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

section GenericObserved
variable {I E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

private def observedCesaro (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H) (N : ℕ) (u : E) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖J ((T ^ n) u)‖ ^ (2 : ℕ)

private theorem observed_amplitude_zero_iff
    (a : I → E →L[ℂ] ℂ) (v : I → E) (J : E →L[ℂ] H)
    (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hW : ∀ u i, W u i = (‖J (v i)‖ : ℂ) * a i u) (u : E) :
    W u = 0 ↔ ∀ i, a i u = 0 ∨ J (v i) = 0 := by
  constructor
  · intro h i
    have hw := congrArg (fun f : lp (fun _ : I => ℂ) 2 => f i) h
    rw [hW] at hw
    change (‖J (v i)‖ : ℂ) * a i u = 0 at hw
    rcases mul_eq_zero.1 hw with hj | ha
    · exact Or.inr (by simpa only [Complex.ofReal_eq_zero, norm_eq_zero] using hj)
    · exact Or.inl ha
  · intro h
    apply lp.ext
    funext i
    rw [hW]
    rcases h i with ha | hj
    · simp only [ha, mul_zero, lp.coeFn_zero, Pi.zero_apply]
    · simp only [hj, norm_zero, Complex.ofReal_zero, zero_mul, lp.coeFn_zero, Pi.zero_apply]

private theorem observed_amplitude_shift_norm
    (T : E ≃ₗᵢ[ℂ] E) (a : I → E →L[ℂ] ℂ) (v : I → E) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (ha : ∀ i u, a i (T u) = z i * a i u)
    (J : E →L[ℂ] H) (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hW : ∀ u, ‖W u‖ ^ (2 : ℕ) = ∑' i, ‖a i u‖ ^ (2 : ℕ) * ‖J (v i)‖ ^ (2 : ℕ)) (u : E) :
    ‖W (T u)‖ = ‖W u‖ := by
  have hs : ‖W (T u)‖ ^ (2 : ℕ) = ‖W u‖ ^ (2 : ℕ) := by
    rw [hW, hW]
    apply tsum_congr
    intro i
    rw [ha, norm_mul, hz, one_mul]
  nlinarith [norm_nonneg (W (T u)), norm_nonneg (W u)]

private theorem observed_amplitude_pow_norm
    (T : E ≃ₗᵢ[ℂ] E) (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hW : ∀ u, ‖W (T u)‖ = ‖W u‖) (u : E) (n : ℕ) :
    ‖W ((T ^ n) u)‖ = ‖W u‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change ‖W (T ((T ^ n) u))‖ = _
    rw [hW, ih]

private theorem observed_mean_zero_iff
    (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H) (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hm : ∀ u, Tendsto (fun N => observedCesaro T J N u) atTop (𝓝 (‖W u‖ ^ (2 : ℕ))))
    (u : E) : Tendsto (fun N => observedCesaro T J N u) atTop (𝓝 0) ↔ W u = 0 := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (hm u) h
    have hn : ‖W u‖ = 0 := by nlinarith [norm_nonneg (W u)]
    exact norm_eq_zero.1 hn
  · intro h
    simpa only [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hm u

private theorem observed_amplitude_injective_iff [DecidableEq I]
    (a : I → E →L[ℂ] ℂ) (ha : Function.Injective (fun u => fun i => a i u))
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (J : E →L[ℂ] H)
    (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hW : ∀ u, W u = 0 ↔ ∀ i, a i u = 0 ∨ J (v i) = 0)
    (hm : ∀ i, W (v i) = lp.single 2 i (‖J (v i)‖ : ℂ)) :
    Function.Injective W ↔ ∀ i, J (v i) ≠ 0 := by
  constructor
  · intro hi i hj
    have hz : W (v i) = 0 := by
      rw [hm, hj, norm_zero, Complex.ofReal_zero]
      simp
    have he : v i = 0 := hi (by simpa only [map_zero] using hz)
    have hn := hv i
    rw [he, norm_zero] at hn
    norm_num at hn
  · intro hj x y hxy
    have hz : W (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hs := (hW (x - y)).1 hz
    apply ha
    funext i
    have hc : a i (x - y) = 0 := (hs i).resolve_right (hj i)
    simpa only [map_sub, sub_eq_zero] using hc

private theorem observed_zero_orbit_iff
    (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H) (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hm : ∀ u, Tendsto (fun N => observedCesaro T J N u) atTop (𝓝 0) ↔ W u = 0)
    (hp : ∀ u n, ‖W ((T ^ n) u)‖ = ‖W u‖)
    (hJ : ∀ u, W u = 0 → J u = 0) (u : E) :
    Tendsto (fun N => observedCesaro T J N u) atTop (𝓝 0) ↔
      ∀ n : ℕ, J ((T ^ n) u) = 0 := by
  constructor
  · intro h n
    have hz := (hm u).1 h
    apply hJ
    apply norm_eq_zero.1
    rw [hp, hz, norm_zero]
  · intro h
    simpa only [observedCesaro, h, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

private theorem observed_observable_iff_injective
    (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H) (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hm : ∀ u, Tendsto (fun N => observedCesaro T J N u) atTop (𝓝 0) ↔ W u = 0) :
    (∀ u : E, Tendsto (fun N => observedCesaro T J N u) atTop (𝓝 0) ↔ u = 0) ↔
      Function.Injective W := by
  constructor
  · intro h x y he
    have hz : W (x - y) = 0 := by rw [map_sub, he, sub_self]
    exact sub_eq_zero.1 ((h (x - y)).1 ((hm (x - y)).2 hz))
  · intro hi u
    rw [hm]
    constructor
    · intro h
      exact hi (by simpa only [map_zero] using h)
    · rintro rfl
      exact map_zero _
end GenericObserved

private theorem closed_subtype_observation_zero
    {I B H : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (X : Submodule ℂ B) (hX : IsClosed (X : Set B))
    (v : I → X) (J : X →L[ℂ] H) (hv : ∀ i, J (v i) = 0) (u : X)
    (hu : u.val ∈ (Submodule.span ℂ (Set.range (fun i => (v i).val))).topologicalClosure) :
    J u = 0 := by
  let D : Submodule ℂ B := J.ker.map X.subtype
  have hD : IsClosed (D : Set B) :=
    (X.isClosedEmbedding_subtype hX).isClosedMap _ J.isClosed_ker
  have hle : (Submodule.span ℂ (Set.range (fun i => (v i).val))).topologicalClosure ≤ D := by
    apply hD.closure_subset_iff.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, hv i, rfl⟩
  obtain ⟨w, hw, hwu⟩ := hle hu
  have he : w = u := Subtype.ext hwu
  exact he ▸ hw



private theorem actual_observation_zero_of_spectrum
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b)
    (h : ∀ ω : ℝ, causalFrequencyCoefficient b ω u = 0 ∨ J (causalFrequencyMode b ω) = 0) :
    J u = 0 := by
  let A := Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u)
  exact closed_subtype_observation_zero (causalFrequencySpace b)
    (causalFrequencyCore b).isClosed_topologicalClosure
    (fun ω : A => causalFrequencyMode b ω.val) J
    (fun ω => (h ω.val).resolve_left ω.property) u
    (causalFrequencySpace_mem_closed_span_support b u)

/-- Weighted spectral energy vanishes exactly when every occupied frequency
is invisible to the observer. -/
theorem causalFrequencyObservedAmplitude_eq_zero_iff
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    causalFrequencyObservedAmplitude b J u = 0 ↔
      ∀ ω : ℝ, causalFrequencyCoefficient b ω u = 0 ∨ J (causalFrequencyMode b ω) = 0 :=
  observed_amplitude_zero_iff (causalFrequencyCoefficient b) (causalFrequencyMode b) J
    (causalFrequencyObservedAmplitude b J) (causalFrequencyObservedAmplitude_apply b J) u

/-- Weighted energy is conserved by every derivative-shift step even when
the observer does not commute with the shift. -/
theorem causalFrequencyObservedAmplitude_shift_norm
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    ‖causalFrequencyObservedAmplitude b J (causalFrequencyShift b u)‖ =
      ‖causalFrequencyObservedAmplitude b J u‖ :=
  observed_amplitude_shift_norm (causalFrequencyShift b) (causalFrequencyCoefficient b)
    (causalFrequencyMode b) (fun ω => (causalUnitBoundaryRate b ω).val)
    (norm_causalUnitBoundaryRate b) (causalFrequencyCoefficient_shift b) J
    (causalFrequencyObservedAmplitude b J) (causalFrequencyObservedAmplitude_square_norm b J) u

/-- Every nonnegative derivative-shift iterate has the same weighted spectral
energy as the original completed vector. -/
theorem causalFrequencyObservedAmplitude_pow_norm
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) (n : ℕ) :
    ‖causalFrequencyObservedAmplitude b J (((causalFrequencyShift b) ^ n) u)‖ =
      ‖causalFrequencyObservedAmplitude b J u‖ :=
  observed_amplitude_pow_norm (causalFrequencyShift b) (causalFrequencyObservedAmplitude b J)
    (causalFrequencyObservedAmplitude_shift_norm b J) u n

/-- A Hilbert observation has zero Cesaro energy exactly when its weighted
amplitude vector vanishes. -/
theorem causalFrequencyShift_completed_hilbert_mean_zero_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J (((causalFrequencyShift b) ^ n) u)‖ ^ (2 : ℕ)) atTop (𝓝 0) ↔
      causalFrequencyObservedAmplitude b J u = 0 :=
  observed_mean_zero_iff (causalFrequencyShift b) J (causalFrequencyObservedAmplitude b J)
    (causalFrequencyShift_completed_hilbert_square_mean b J) u

/-- Exact spectral classification of all completed states with vanishing
observed time-averaged energy. -/
theorem causalFrequencyShift_completed_hilbert_zero_spectrum_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J (((causalFrequencyShift b) ^ n) u)‖ ^ (2 : ℕ)) atTop (𝓝 0) ↔
      ∀ ω : ℝ, causalFrequencyCoefficient b ω u = 0 ∨ J (causalFrequencyMode b ω) = 0 :=
  (causalFrequencyShift_completed_hilbert_mean_zero_iff b J u).trans
    (causalFrequencyObservedAmplitude_eq_zero_iff b J u)

/-- The observed-amplitude map is faithful exactly when no individual actual
frequency mode is invisible. This criterion remains exact after completion. -/
theorem causalFrequencyObservedAmplitude_injective_iff
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) :
    Function.Injective (causalFrequencyObservedAmplitude b J) ↔
      ∀ ω : ℝ, J (causalFrequencyMode b ω) ≠ 0 :=
  observed_amplitude_injective_iff (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_injective b) (causalFrequencyMode b)
    (norm_causalBoundedUnitEigenchain b) J (causalFrequencyObservedAmplitude b J)
    (causalFrequencyObservedAmplitude_eq_zero_iff b J)
    (fun ω => causalFrequencyObservedAmplitude_mode b ω J)

/-- On this recurrent completed frequency space, zero observed mean energy
means that the entire observed orbit vanishes, including its initial value. -/
theorem causalFrequencyShift_completed_hilbert_zero_orbit_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J (((causalFrequencyShift b) ^ n) u)‖ ^ (2 : ℕ)) atTop (𝓝 0) ↔
      ∀ n : ℕ, J (((causalFrequencyShift b) ^ n) u) = 0 :=
  observed_zero_orbit_iff (causalFrequencyShift b) J (causalFrequencyObservedAmplitude b J)
    (causalFrequencyShift_completed_hilbert_mean_zero_iff b J)
    (causalFrequencyObservedAmplitude_pow_norm b J)
    (fun w hw => actual_observation_zero_of_spectrum b J w
      ((causalFrequencyObservedAmplitude_eq_zero_iff b J w).1 hw)) u

/-- Exact observability criterion: zero mean energy detects only the zero
completed state precisely when the observer sees every single frequency mode. -/
theorem causalFrequencyShift_completed_hilbert_observable_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) :
    (∀ u : causalFrequencySpace b,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖J (((causalFrequencyShift b) ^ n) u)‖ ^ (2 : ℕ)) atTop (𝓝 0) ↔ u = 0) ↔
      ∀ ω : ℝ, J (causalFrequencyMode b ω) ≠ 0 :=
  (observed_observable_iff_injective (causalFrequencyShift b) J
    (causalFrequencyObservedAmplitude b J)
    (causalFrequencyShift_completed_hilbert_mean_zero_iff b J)).trans
      (causalFrequencyObservedAmplitude_injective_iff b J)

end RHTower.FokasLenells
