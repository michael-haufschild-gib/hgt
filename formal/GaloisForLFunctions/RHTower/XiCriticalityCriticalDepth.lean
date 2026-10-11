import GaloisForLFunctions.RHTower.XiCriticalityEveryScale
import GaloisForLFunctions.RHTower.ZetaCriticalAsymptotics

/-!
# The critical-scale anti-crystal law and resonances at depth `C / log T`

**Theorem** (`exists_eventually_not_rigidWindow_critical`). There is `C > 0` such that for all large
`T`, the ordered zeros of `ζ` with ordinates in `[T^{1/2}, T³]` are not `C/log T`-rigid. Rigidity
means that consecutive gaps `g, g'` satisfy `g' ≤ g e^{(g + g')/h}`. So `C/log T`-rigidity says
that, at the mean-spacing scale, the normalized gaps change by a factor `1 + O(1/C)` from one
zero to the next.

**Proof.** Combine `false_of_critical_facts` with the large-`T` inputs of
`ZetaCriticalAsymptotics`. Rigidity on the window gives RH there and a local lattice structure
around every height where the Selberg polynomial is small. On a lattice the Fejér pair rows of
Montgomery's averaged form cancel by Poisson summation. The averaged form is still
`≥ (1/2)(T/2π)(L/8)`.

**Corollary** (`exists_eventually_shallow_resonance_critical`). Let `E` be strict lower Pólya,
nonzero on `ℝ`, with `Re E = Ξ` on `ℝ`. There are `C > 0` and `K` such that for all large `T`, `E`
has a zero `z` with `T^{1/2} − 1 ≤ Re z ≤ T³ + K` and `Im z ≥ −C/log T`. A resonance-free box of
depth `2C/log T` would make the window `C/log T`-rigid (`rigidWindow_of_resonance_free`).
-/

open Complex Filter Topology Set

namespace RHTower

/-- **The critical-scale anti-crystal law.** -/
theorem exists_eventually_not_rigidWindow_critical :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ¬ RigidWindow (C / Real.log T) T := by
  refine ⟨10 ^ 60, by norm_num, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 25),
    eventually_ge_atTop (2 : ℝ), eventually_narrowMass_bound, eventually_lorentzMassW_le,
    eventually_selbergLength_le,
    eventually_re_averagedMontgomeryForm_ge (α₀ := 1 / 8) (R := 16) (ε := 1 / 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    eventually_lowPairs_le, eventually_edges_le, eventually_card_zeroWindow_le]
    with T hL hT2 hV hW hlen hM hlow hedge hcount hrig
  have hT0 : 0 < T := by linarith
  have hx1 : 1 < T ^ (1 / 20 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hlx : Real.log (T ^ (1 / 20 : ℝ)) = Real.log T / 20 := by
    rw [Real.log_rpow hT0]; ring
  have hRH : ∀ q : XiZeroCopy, T ^ (1 / 2 : ℝ) ≤ (q.1 : ℂ).im → (q.1 : ℂ).im ≤ T ^ 3 →
      (q.1 : ℂ).re = 1 / 2 := fun q h1 h2 =>
    re_eq_half_of_rigidWindow hrig h1 h2 (lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) h1)
  exact false_of_critical_facts (by linarith) hL hx1 hlx (hV hRH) hW hlen hM hlow hedge hcount hrig

/-- **Resonances within depth `C / log T`.** -/
theorem exists_eventually_shallow_resonance_critical {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) (hne : ∀ t : ℝ, E t ≠ 0) :
    ∃ C K : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∃ z : ℂ, E z = 0 ∧
      T ^ (1 / 2 : ℝ) - 1 ≤ z.re ∧ z.re ≤ T ^ 3 + K ∧ -(C / Real.log T) ≤ z.im := by
  obtain ⟨w, hw, T₁, -, hgap2, hzwin⟩ := exists_ordinate_window_facts
  obtain ⟨K, hK0, hnot⟩ := exists_eventually_not_rigidWindow_critical
  refine ⟨2 * K, 2 * w + 1, by positivity, ?_⟩
  have eX := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop T₁
  have eV : ∀ᶠ T : ℝ in atTop, 2 * K ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [hnot, eX, eventually_ge_atTop (1 : ℝ), eV] with T hnotT hXT hT1 hv
  have hv0 : 0 < Real.log T := by linarith
  have hd0 : 0 < 2 * K / Real.log T := by positivity
  have hd1 : 2 * K / Real.log T ≤ 1 := by rw [div_le_one hv0]; exact hv
  by_contra hcon
  push Not at hcon
  apply hnotT
  have hR := rigidWindow_of_resonance_free hE hrep hne hgap2 hzwin hw hd0 hXT hT1 hcon
  have e : min (2 * K / Real.log T) 1 / 2 = K / Real.log T := by
    rw [min_eq_left hd1]; ring
  rwa [e] at hR

end RHTower
