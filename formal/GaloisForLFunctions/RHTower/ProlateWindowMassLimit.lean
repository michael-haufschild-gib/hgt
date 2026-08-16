import GaloisForLFunctions.RHTower.ProlateWindowMass
import GaloisForLFunctions.RHTower.ProlateOscProfileLimit
import GaloisForLFunctions.HTGeometry.WindowProductLimit
import GaloisForLFunctions.HTGeometry.SquareIntegrableOfWindowLimits
import GaloisForLFunctions.HTGeometry.EvenRungCounting

/-!
# Window masses of the rescaled prolate profiles converge

The Grönwall window comparison controls `|u_i − oscProfile m|` on `[0,K]` by the envelope, evenness
carries that to `[−K,K]`, and the uniform phase bound supplies the other factor.  So the window
masses converge to the window mass of the limit profile.

This is the convergence hypothesis consumed twice in the differential-ordering argument: once to
make the limit profile square integrable, once to make the pairings of two distinct modes converge.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Window masses converge to the window mass of the limit profile.** -/
theorem tendsto_prolateWindowMass {ι : Type*} {L : Filter ι}
    {mu c : ι → ℝ} {K B m : ℝ} {u u' u'' : ι → ℝ → ℝ}
    (hK : 0 < K) (hB : 0 ≤ B)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (heu : ∀ i, Function.Even (u i))
    (hev : ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧ u i 0 = 1 ∧ u' i 0 = 0)
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    Tendsto (fun i => ∫ x in (-K)..K, u i x * u i x) L
      (𝓝 (∫ x in (-K)..K, oscProfile m x * oscProfile m x)) := by
  have hKK : (-K : ℝ) ≤ K := by linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
    (continuous_oscProfile m).continuousOn
  have hvc : ContinuousOn (oscProfile m) (uIcc (-K) K) := (continuous_oscProfile m).continuousOn
  have hwb : ∀ x ∈ Icc (-K) K, |oscProfile m x| ≤ C := by
    intro x hx
    have := hC x hx
    rwa [Real.norm_eq_abs] at this
  refine tendsto_intervalIntegral_product_eventually (E := fun i =>
    oscWindowEnvelope (c i) (mu i) m K B) (B := B) (C := C) hKK hvc hvc hwb hB ?_
    (tendsto_oscWindowEnvelope hmu hc)
  filter_upwards [hev] with i hi
  obtain ⟨hcpos, hcK, hequ, hBi, h0, h0'⟩ := hi
  have hcu : Continuous (u i) := Differentiable.continuous fun x => (hu i x).differentiableAt
  have hdist0 : ∀ x ∈ Icc (0 : ℝ) K,
      |u i x - oscProfile m x| ≤ oscWindowEnvelope (c i) (mu i) m K B := by
    intro x hx
    exact le_trans (le_max_left _ _)
      (prolateProfile_window_osc_dist_le (m := m) hK hcK (hu i) (hu' i) hequ hBi h0 h0' x hx)
  refine ⟨hcu.continuousOn, hcu.continuousOn,
    abs_sub_le_of_even_window' (heu i) (even_oscProfile m) hdist0,
    abs_sub_le_of_even_window' (heu i) (even_oscProfile m) hdist0,
    abs_le_of_even_window (heu i) (fun x hx => le_trans (le_max_left _ _) (hBi x hx)),
    oscWindowEnvelope_nonneg hcpos hK hB⟩

/-- **Cross pairings converge.**  For two prolate families the window pairings converge to the
pairing of their limit profiles. -/
theorem tendsto_prolateWindowPairing {ι : Type*} {L : Filter ι}
    {mu nu c : ι → ℝ} {K B m m' : ℝ} {u u' u'' v v' v'' : ι → ℝ → ℝ}
    (hK : 0 < K) (hB : 0 ≤ B)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hv : ∀ i x, HasDerivAt (v i) (v' i x) x) (hv' : ∀ i x, HasDerivAt (v' i) (v'' i x) x)
    (heu : ∀ i, Function.Even (u i)) (hevn : ∀ i, Function.Even (v i))
    (hevu : ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧ u i 0 = 1 ∧ u' i 0 = 0)
    (hevv : ∀ᶠ i in L, 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, v'' i x = rescaledProlateP (c i) (nu i) x * v i x
        + rescaledProlateQ (c i) x * v' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |v i x| |v' i x| ≤ B) ∧ v i 0 = 1 ∧ v' i 0 = 0)
    (hmu : Tendsto mu L (𝓝 m)) (hnu : Tendsto nu L (𝓝 m')) (hc : Tendsto c L atTop) :
    Tendsto (fun i => ∫ x in (-K)..K, u i x * v i x) L
      (𝓝 (∫ x in (-K)..K, oscProfile m x * oscProfile m' x)) := by
  have hKK : (-K : ℝ) ≤ K := by linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
    (continuous_oscProfile m').continuousOn
  have hwb : ∀ x ∈ Icc (-K) K, |oscProfile m' x| ≤ C := by
    intro x hx
    have := hC x hx
    rwa [Real.norm_eq_abs] at this
  have hEtend : Tendsto (fun i => oscWindowEnvelope (c i) (mu i) m K B
      + oscWindowEnvelope (c i) (nu i) m' K B) L (𝓝 0) := by
    have h := (tendsto_oscWindowEnvelope (K := K) (B := B) hmu hc).add
      (tendsto_oscWindowEnvelope (K := K) (B := B) hnu hc)
    simpa using h
  refine tendsto_intervalIntegral_product_eventually (E := fun i =>
    oscWindowEnvelope (c i) (mu i) m K B + oscWindowEnvelope (c i) (nu i) m' K B)
    (B := B) (C := C) hKK (continuous_oscProfile m).continuousOn
    (continuous_oscProfile m').continuousOn hwb hB ?_ hEtend
  filter_upwards [hevu, hevv] with i hiu hiv
  obtain ⟨hcpos, hcK, hequ, hBi, h0, h0'⟩ := hiu
  obtain ⟨-, heqv, hBv, hv0, hv0'⟩ := hiv
  have hcu : Continuous (u i) := Differentiable.continuous fun x => (hu i x).differentiableAt
  have hcv : Continuous (v i) := Differentiable.continuous fun x => (hv i x).differentiableAt
  have hEu : 0 ≤ oscWindowEnvelope (c i) (mu i) m K B := oscWindowEnvelope_nonneg hcpos hK hB
  have hEv : 0 ≤ oscWindowEnvelope (c i) (nu i) m' K B := oscWindowEnvelope_nonneg hcpos hK hB
  have hdu : ∀ x ∈ Icc (-K) K, |u i x - oscProfile m x|
      ≤ oscWindowEnvelope (c i) (mu i) m K B + oscWindowEnvelope (c i) (nu i) m' K B := by
    refine abs_sub_le_of_even_window' (heu i) (even_oscProfile m) fun x hx => ?_
    have hthis : |u i x - oscProfile m x| ≤ oscWindowEnvelope (c i) (mu i) m K B := by
      rw [oscWindowEnvelope]
      exact le_trans (le_max_left _ _)
        (prolateProfile_window_osc_dist_le (m := m) hK hcK (hu i) (hu' i) hequ hBi h0 h0' x hx)
    linarith [hthis, hEv]
  have hdv : ∀ x ∈ Icc (-K) K, |v i x - oscProfile m' x|
      ≤ oscWindowEnvelope (c i) (mu i) m K B + oscWindowEnvelope (c i) (nu i) m' K B := by
    refine abs_sub_le_of_even_window' (hevn i) (even_oscProfile m') fun x hx => ?_
    have hthis : |v i x - oscProfile m' x| ≤ oscWindowEnvelope (c i) (nu i) m' K B := by
      rw [oscWindowEnvelope]
      exact le_trans (le_max_left _ _)
        (prolateProfile_window_osc_dist_le (m := m') hK hcK (hv i) (hv' i) heqv hBv hv0 hv0' x hx)
    linarith [hthis, hEu]
  exact ⟨hcu.continuousOn, hcv.continuousOn, hdu, hdv,
    abs_le_of_even_window (heu i) (fun x hx => le_trans (le_max_left _ _) (hBi x hx)),
    add_nonneg hEu hEv⟩

/-- **The limiting separation constant of a prolate family is an even rung.**  This is the
eigenvalue half of the prolate-to-Hermite limit, for one family: the window masses converge to those
of the limit profile, a uniform mass bound makes that profile square integrable, and rigidity puts
its separation constant on the even ladder. -/
theorem exists_evenRung_of_prolate_family {ι : Type*} {L : Filter ι} [L.NeBot]
    {mu c : ι → ℝ} {B N m : ℝ} {u u' u'' : ι → ℝ → ℝ}
    (hB : 0 ≤ B)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (heu : ∀ i, Function.Even (u i))
    (hev : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧ u i 0 = 1 ∧ u' i 0 = 0)
    (hmass : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, (∫ x in (-K)..K, u i x * u i x) ≤ N)
    (hmu : Tendsto mu L (𝓝 m)) (hc : Tendsto c L atTop) :
    ∃ n : ℕ, Even n ∧ m = 2 * (n : ℝ) + 1 := by
  have hconv : ∀ K : ℝ, 0 < K →
      Tendsto (fun i => ∫ x in (-K)..K, u i x * u i x) L
        (𝓝 (∫ x in (-K)..K, oscProfile m x * oscProfile m x)) :=
    fun K hK => tendsto_prolateWindowMass hK hB hu hu' heu (hev K hK) hmu hc
  exact even_rung_of_integrable_oscProfile
    (integrable_sq_of_bounded_window_limits (continuous_oscProfile m) hconv hmass)

/-- **Two orthogonal prolate families have distinct limits.**  If their window pairings are
`O(K⁻²)` — which exact orthogonality on the rescaled window plus the second-moment tail bound
supplies — then a common limit would force the limit profile to have vanishing window mass. -/
theorem prolateFamily_limit_ne {ι : Type*} {L : Filter ι} [L.NeBot]
    {mu nu c : ι → ℝ} {B C m m' : ℝ} {u u' u'' v v' v'' : ι → ℝ → ℝ}
    (hB : 0 ≤ B)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (hv : ∀ i x, HasDerivAt (v i) (v' i x) x) (hv' : ∀ i x, HasDerivAt (v' i) (v'' i x) x)
    (heu : ∀ i, Function.Even (u i)) (hevn : ∀ i, Function.Even (v i))
    (hevu : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧ u i 0 = 1 ∧ u' i 0 = 0)
    (hevv : ∀ K : ℝ, 0 < K → ∀ᶠ i in L, 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, v'' i x = rescaledProlateP (c i) (nu i) x * v i x
        + rescaledProlateQ (c i) x * v' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |v i x| |v' i x| ≤ B) ∧ v i 0 = 1 ∧ v' i 0 = 0)
    (hpair : ∀ K : ℝ, 0 < K → ∀ᶠ i in L,
      |∫ x in (-K)..K, u i x * v i x| ≤ C / K ^ 2)
    (hmu : Tendsto mu L (𝓝 m)) (hnu : Tendsto nu L (𝓝 m')) (hc : Tendsto c L atTop) :
    m ≠ m' := by
  intro heq
  subst heq
  refine false_of_orthogonal_same_limit (C := C) (v := oscProfile m) ?_ hpair
    (integral_oscProfile_mul_self_pos m one_pos)
    (fun K hK => integral_oscProfile_mul_self_mono m hK)
  intro K hK
  exact tendsto_prolateWindowPairing hK hB hu hu' hv hv' heu hevn
    (hevu K hK) (hevv K hK) hmu hnu hc

/-- **The counting contradiction for a family of prolate modes.**  There is no family of `j+1`
prolate mode families with distinct limiting separation constants all below `4j+1`: each limit is an
even rung, and only `j` even rungs lie there. -/
theorem false_of_prolateFamily_below {j : ℕ} {ι : Type*} {L : Filter ι} [L.NeBot]
    {c : ι → ℝ} {mu : Fin (j + 1) → ι → ℝ} {m : Fin (j + 1) → ℝ} {B N : ℝ}
    {u u' u'' : Fin (j + 1) → ι → ℝ → ℝ}
    (hB : 0 ≤ B)
    (hu : ∀ k i x, HasDerivAt (u k i) (u' k i x) x)
    (hu' : ∀ k i x, HasDerivAt (u' k i) (u'' k i x) x)
    (heu : ∀ k i, Function.Even (u k i))
    (hev : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' k i x = rescaledProlateP (c i) (mu k i) x * u k i x
        + rescaledProlateQ (c i) x * u' k i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u k i x| |u' k i x| ≤ B) ∧ u k i 0 = 1 ∧ u' k i 0 = 0)
    (hmass : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ i in L,
      (∫ x in (-K)..K, u k i x * u k i x) ≤ N)
    (hmu : ∀ k, Tendsto (mu k) L (𝓝 (m k))) (hc : Tendsto c L atTop)
    (hdistinct : Function.Injective m)
    (hbelow : ∀ k, m k < 4 * (j : ℝ) + 1) :
    False := by
  refine not_injective_evenRung_below m (fun k => ?_) hbelow hdistinct
  obtain ⟨n, hne, hm⟩ := exists_evenRung_of_prolate_family hB (hu k) (hu' k) (heu k)
    (hev k) (hmass k) (hmu k) hc
  exact ⟨n, hne, hm⟩

/-- **`(α)`'s lower half.**  There is no family of `j+1` pairwise orthogonal prolate mode families
whose limiting separation constants all lie below `4j+1`.  Distinctness of the limits is derived
from the orthogonality, so the only hypotheses left are ones the prolate modes satisfy. -/
theorem false_of_orthogonal_prolateFamily_below {j : ℕ} {ι : Type*} {L : Filter ι} [L.NeBot]
    {c : ι → ℝ} {mu : Fin (j + 1) → ι → ℝ} {m : Fin (j + 1) → ℝ} {B N C : ℝ}
    {u u' u'' : Fin (j + 1) → ι → ℝ → ℝ}
    (hB : 0 ≤ B)
    (hu : ∀ k i x, HasDerivAt (u k i) (u' k i x) x)
    (hu' : ∀ k i x, HasDerivAt (u' k i) (u'' k i x) x)
    (heu : ∀ k i, Function.Even (u k i))
    (hev : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' k i x = rescaledProlateP (c i) (mu k i) x * u k i x
        + rescaledProlateQ (c i) x * u' k i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u k i x| |u' k i x| ≤ B) ∧ u k i 0 = 1 ∧ u' k i 0 = 0)
    (hmass : ∀ (k : Fin (j + 1)) (K : ℝ), 0 < K → ∀ᶠ i in L,
      (∫ x in (-K)..K, u k i x * u k i x) ≤ N)
    (hpair : ∀ k l : Fin (j + 1), k ≠ l → ∀ K : ℝ, 0 < K → ∀ᶠ i in L,
      |∫ x in (-K)..K, u k i x * u l i x| ≤ C / K ^ 2)
    (hmu : ∀ k, Tendsto (mu k) L (𝓝 (m k))) (hc : Tendsto c L atTop)
    (hbelow : ∀ k, m k < 4 * (j : ℝ) + 1) :
    False := by
  have hdistinct : Function.Injective m := by
    intro k l hkl
    by_contra hne
    refine prolateFamily_limit_ne (C := C) hB (hu k) (hu' k) (hu l) (hu' l) (heu k) (heu l)
      (hev k) (fun K hK => (hev l K hK).mono fun i hi =>
        ⟨hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2⟩)
      (hpair k l hne) (hmu k) (hmu l) hc hkl
  exact false_of_prolateFamily_below (N := N) hB hu hu' heu hev hmass hmu hc hdistinct hbelow

end RHTower
