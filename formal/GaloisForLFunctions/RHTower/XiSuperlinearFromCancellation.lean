import GaloisForLFunctions.HTGeometry.GridCancellationZeroCount
import GaloisForLFunctions.RHTower.XiCSchwartzRestriction
import GaloisForLFunctions.RHTower.XiRealDivisorSampling
import GaloisForLFunctions.RHTower.XiSamplingIdealizerCollapse

/-!
# Superlinear real Xi density from grid cancellation

`prime-modulated-weyl-idealizer-collapse-on-xi-sampling`, section 4.

Theorem A needs the real `Xi` divisor to have a superlinear counting function, equation `(22)`.
This module reduces that single literature input to a purely analytic statement about `Xi` itself:
for every rate `c` there must be one window `[a, a + N H]` on which the absolute mass of `Xi`
exceeds the total cancellation of its signed integrals over the grid of mesh `H` by more than
`c · (a + N H) · Mx`, where `Mx` bounds the absolute mass of one cell.

No zero-counting, no functional equation and no mean-value theorem enters the reduction: the whole
content is the grid cancellation device of `GridCancellationZeroCount`, plus local finiteness of the
divisor, which this tree already owns.
-/

open MeasureTheory Set GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The real restriction of the centered `Xi` is continuous. -/
theorem continuous_Xi_real : Continuous Xi := by
  have h : Xi = fun t : ℝ => (XiC (t : ℂ)).re := by
    funext t
    rw [XiC_ofReal]
    simp
  rw [h]
  exact Complex.continuous_re.comp continuous_XiC_ofReal

theorem xi_eq_zero_iff_mem_xiRealDivisor {t : ℝ} : Xi t = 0 ↔ t ∈ xiRealDivisor := by
  simp only [xiRealDivisor, Set.mem_setOf_eq, XiC_ofReal]
  constructor
  · intro h; rw [h]; norm_num
  · intro h; exact_mod_cast h

/-- Any finite set of real `Xi` zeros inside the window is counted by the sampling count. -/
theorem card_le_samplingCount_xiRealDivisor {T : ℝ} (Zs : Finset ℝ)
    (hZ : ∀ x ∈ Zs, |x| ≤ T ∧ Xi x = 0) : Zs.card ≤ samplingCount xiRealDivisor T := by
  rw [samplingCount, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (locallyFiniteSamples_xiRealDivisor T)
  intro x hx
  obtain ⟨habs, hzero⟩ := hZ x (by simpa using hx)
  obtain ⟨h1, h2⟩ := abs_le.mp habs
  exact ⟨xi_eq_zero_iff_mem_xiRealDivisor.mp hzero, Set.mem_Icc.mpr ⟨h1, h2⟩⟩

/-- **The grid-cancellation input.**  For every rate `c` there is a window `[a, a + N H]` of height
at least one on which the absolute mass of `f` exceeds the total cancellation of its signed
integrals over the grid of mesh `H` by more than `c · (a + N H) · Mx`, where `Mx` bounds the
absolute mass of a single cell. -/
def GridCancellationSurplus (f : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, ∃ (a H : ℝ) (N : ℕ) (L Bsum Mx : ℝ),
    0 < H ∧ 0 ≤ a ∧ 1 ≤ a + (N : ℝ) * H ∧ 0 < Mx ∧
    L ≤ (∫ t in a..(a + (N : ℝ) * H), |f t|) ∧
    (∑ j ∈ Finset.range N,
      |∫ t in (a + (j : ℝ) * H)..(a + ((j : ℝ) + 1) * H), f t|) ≤ Bsum ∧
    (∀ j ∈ Finset.range N,
      (∫ t in (a + (j : ℝ) * H)..(a + ((j : ℝ) + 1) * H), |f t|) ≤ Mx) ∧
    c * (a + (N : ℝ) * H) * Mx < L - Bsum

/-- **Reduction of `(22)` to grid cancellation.**  Let `f` be any continuous real function whose
zeros are `Xi`-zeros — `Xi` itself, `Xi` times a positive weight, a mollified Hardy function, a
clamp of any of these.  A single family of windows on which the absolute mass of `f` beats its grid
cancellation by a superlinear margin gives the superlinear sampling density of the real `Xi`
divisor, hence Theorem A applies. -/
theorem superlinearSamples_xiRealDivisor_of_grid_cancellation
    (f : ℝ → ℝ) (hf : Continuous f) (hfz : ∀ t : ℝ, f t = 0 → Xi t = 0)
    (h : GridCancellationSurplus f) :
    SuperlinearSamples xiRealDivisor := by
  intro c
  obtain ⟨a, H, N, L, Bsum, Mx, hH, ha, hT, hMxpos, hL, hB, hMx, hgain⟩ := h c
  obtain ⟨Zs, hZmem, hZcard⟩ := exists_finset_zeros_card_mul_ge hH hf.continuousOn hL hB hMx
  refine ⟨a + (N : ℝ) * H, hT, ?_⟩
  have hcard : Zs.card ≤ samplingCount xiRealDivisor (a + (N : ℝ) * H) := by
    refine card_le_samplingCount_xiRealDivisor Zs ?_
    intro x hx
    obtain ⟨hmem, hzero⟩ := hZmem x hx
    refine ⟨abs_le.mpr ⟨?_, hmem.2.le⟩, hfz x hzero⟩
    linarith [hmem.1]
  have h1 : c * (a + (N : ℝ) * H) * Mx < (Zs.card : ℝ) * Mx := lt_of_lt_of_le hgain hZcard
  have h2 : c * (a + (N : ℝ) * H) < (Zs.card : ℝ) := lt_of_mul_lt_mul_right h1 hMxpos.le
  exact lt_of_lt_of_le h2 (by exact_mod_cast hcard)

/-! ## The clamped instance: the cell bound is automatic -/

/-- The two-sided clamp at height `δ`. -/
def clampAt (δ x : ℝ) : ℝ := max (-δ) (min δ x)

theorem continuous_clampAt (δ : ℝ) : Continuous (clampAt δ) := by
  unfold clampAt
  fun_prop

theorem abs_clampAt_le {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : |clampAt δ x| ≤ δ := by
  rw [clampAt, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampAt_eq_zero_iff {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : clampAt δ x = 0 ↔ x = 0 := by
  rw [clampAt]
  constructor
  · intro h
    rcases le_or_gt x 0 with hx | hx
    · rcases le_or_gt (-δ) x with hx' | hx'
      · have : min δ x = x := min_eq_right (by linarith)
        rw [this, max_eq_right hx'] at h
        exact h
      · have : min δ x = x := min_eq_right (by linarith)
        rw [this, max_eq_left hx'.le] at h
        linarith
    · have : min δ x = min δ x := rfl
      have hmin : 0 < min δ x := lt_min hδ hx
      rw [max_eq_right (by linarith : -δ ≤ min δ x)] at h
      linarith
  · intro h
    rw [h, min_eq_right hδ.le, max_eq_right (by linarith : -δ ≤ (0:ℝ))]

/-- On any cell of length `H` the clamped absolute mass is at most `δ H`. -/
theorem integral_abs_clampAt_le {δ : ℝ} (hδ : 0 ≤ δ) {g : ℝ → ℝ} (hg : Continuous g)
    {u v : ℝ} (huv : u ≤ v) :
    (∫ t in u..v, |clampAt δ (g t)|) ≤ δ * (v - u) := by
  have hint : IntervalIntegrable (fun t => |clampAt δ (g t)|) volume u v :=
    (((continuous_clampAt δ).comp hg).abs).intervalIntegrable u v
  have hmono : (∫ t in u..v, |clampAt δ (g t)|) ≤ ∫ _t in u..v, δ := by
    refine intervalIntegral.integral_mono_on huv hint intervalIntegrable_const ?_
    intro t _
    exact abs_clampAt_le hδ _
  simpa [mul_comm] using hmono

/-- **The clamped reduction.**  Clamping `Xi` at height `δ` keeps every zero and makes the cell
bound automatic, so only two analytic inputs remain: a lower bound for the clamped absolute mass
of the window and an upper bound for the total grid cancellation. -/
theorem superlinearSamples_xiRealDivisor_of_clamped_grid_cancellation
    {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ c : ℝ, ∃ (a H : ℝ) (N : ℕ) (L Bsum : ℝ),
      0 < H ∧ 0 ≤ a ∧ 1 ≤ a + (N : ℝ) * H ∧
      L ≤ (∫ t in a..(a + (N : ℝ) * H), |clampAt δ (Xi t)|) ∧
      (∑ j ∈ Finset.range N,
        |∫ t in (a + (j : ℝ) * H)..(a + ((j : ℝ) + 1) * H), clampAt δ (Xi t)|) ≤ Bsum ∧
      c * (a + (N : ℝ) * H) * (δ * H) < L - Bsum) :
    SuperlinearSamples xiRealDivisor := by
  refine superlinearSamples_xiRealDivisor_of_grid_cancellation
    (fun t => clampAt δ (Xi t)) ((continuous_clampAt δ).comp continuous_Xi_real)
    (fun t ht => (clampAt_eq_zero_iff hδ (Xi t)).mp ht) ?_
  intro c
  obtain ⟨a, H, N, L, Bsum, hH, ha, hT, hL, hB, hgain⟩ := h c
  refine ⟨a, H, N, L, Bsum, δ * H, hH, ha, hT, by positivity, hL, hB, ?_, hgain⟩
  intro j _
  have hle : a + (j : ℝ) * H ≤ a + ((j : ℝ) + 1) * H := by nlinarith [hH.le]
  have := integral_abs_clampAt_le hδ.le continuous_Xi_real hle
  calc (∫ t in (a + (j : ℝ) * H)..(a + ((j : ℝ) + 1) * H), |clampAt δ (Xi t)|)
      ≤ δ * ((a + ((j : ℝ) + 1) * H) - (a + (j : ℝ) * H)) := this
    _ = δ * H := by ring

/-! ## `(23)` from grid cancellation -/

/-- **`(23)` with the literature input replaced by grid cancellation.**  Every coefficient of a
finite shift–Weyl operator descending to the real-Xi sampling quotient vanishes, except the
zero-shift zero-order polynomial multiplier — assuming only that some continuous function whose
zeros are `Xi`-zeros has a superlinear grid-cancellation surplus. -/
theorem xiSamplingIdealizer_collapse_of_grid_cancellation
    {f : ℝ → ℝ} (hf : Continuous f) (hfz : ∀ t : ℝ, f t = 0 → Xi t = 0)
    (hgrid : GridCancellationSurplus f)
    {m : ℕ} {F : Finset ℝ} {coef : ℝ → ℕ → Polynomial ℂ} (h0 : (0 : ℝ) ∈ F)
    (hpres : PreservesSamplingIdeal m xiRealDivisor F coef) :
    ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → coef h j = 0 :=
  xiSamplingIdealizer_collapse
    (superlinearSamples_xiRealDivisor_of_grid_cancellation f hf hfz hgrid) h0 hpres

end RHTower
