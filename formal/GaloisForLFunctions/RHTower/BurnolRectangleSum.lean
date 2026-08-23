import GaloisForLFunctions.RHTower.BurnolRectangleResidue
import GaloisForLFunctions.RHTower.MellinContinuationOrder
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Burnol's rectangle: only the nontrivial zeros and `Z` contribute

Assembling the residue identity for the concrete integrand.  On the rectangle with corners
`1/2 ± A ± iT` the pole set is `{Z, 1, 0} ∪ {zeros of ζ in the rectangle}`; the residues at `1`,
at `0` and at the trivial zeros vanish (`MellinContinuationOrder`), the residue at `Z` is `−M(f)(Z)`
(`BurnolIntegrand`), and what is left is exactly the sum over the nontrivial zeros of height less
than `T`.

## Main results

* `nontrivialZeroFinset` — the zeros `ρ` with `0 < Re ρ < 1` and `|Im ρ| < T`.
* `rectangleIntegral'_burnolIntegrand_extendedMellin` — **the residue identity of Theorem 5.2**.
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The nontrivial zeros below a height -/

/-- The nontrivial zeros of `ζ` of height less than `T`. -/
def nontrivialZeroSet (T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T}

theorem finite_nontrivialZeroSet (T : ℝ) : (nontrivialZeroSet T).Finite := by
  rcases le_or_gt T 0 with hT | hT
  · refine Set.Finite.subset (Set.finite_empty) ?_
    rintro ρ ⟨-, -, -, him⟩
    exact absurd (lt_of_le_of_lt (abs_nonneg _) him) (not_lt.2 hT)
  · refine (finite_riemannZeta_zeros_rectangle (((-T : ℝ) : ℂ) * I) (1 + ((T : ℝ) : ℂ) * I)).subset ?_
    rintro ρ ⟨hz, h1, h2, him⟩
    have hre1 : (((-T : ℝ) : ℂ) * I).re = 0 := by simp
    have him1 : (((-T : ℝ) : ℂ) * I).im = -T := by simp
    have hre2 : ((1 : ℂ) + ((T : ℝ) : ℂ) * I).re = 1 := by simp
    have him2 : ((1 : ℂ) + ((T : ℝ) : ℂ) * I).im = T := by simp
    refine ⟨?_, hz⟩
    rw [mem_Rect (by rw [hre1, hre2]; norm_num) (by rw [him1, him2]; linarith)]
    rw [hre1, him1, hre2, him2]
    have habs := abs_lt.1 him
    exact ⟨h1.le, h2.le, habs.1.le, habs.2.le⟩

/-- The nontrivial zeros of height less than `T`, as a `Finset`. -/
def nontrivialZeroFinset (T : ℝ) : Finset ℂ := (finite_nontrivialZeroSet T).toFinset

theorem mem_nontrivialZeroFinset {T : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZeroFinset T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T := by
  rw [nontrivialZeroFinset, Set.Finite.mem_toFinset]
  exact Iff.rfl

/-! ## The corners -/

/-- Lower left corner of Burnol's rectangle. -/
def burnolRectLow (A T : ℝ) : ℂ := ((1 / 2 - A : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I

/-- Upper right corner of Burnol's rectangle. -/
def burnolRectHigh (A T : ℝ) : ℂ := ((1 / 2 + A : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I

@[simp] theorem burnolRectLow_re (A T : ℝ) : (burnolRectLow A T).re = 1 / 2 - A := by
  simp [burnolRectLow]

@[simp] theorem burnolRectLow_im (A T : ℝ) : (burnolRectLow A T).im = -T := by
  simp [burnolRectLow]

@[simp] theorem burnolRectHigh_re (A T : ℝ) : (burnolRectHigh A T).re = 1 / 2 + A := by
  simp [burnolRectHigh]

@[simp] theorem burnolRectHigh_im (A T : ℝ) : (burnolRectHigh A T).im = T := by
  simp [burnolRectHigh]

theorem mem_burnolRect {A T : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T) (p : ℂ) :
    p ∈ Rectangle (burnolRectLow A T) (burnolRectHigh A T) ↔
      1 / 2 - A ≤ p.re ∧ p.re ≤ 1 / 2 + A ∧ -T ≤ p.im ∧ p.im ≤ T := by
  rw [mem_Rect (by simp; linarith) (by simp; linarith)]
  simp

theorem burnolRect_mem_nhds {A T : ℝ} {p : ℂ}
    (h1 : 1 / 2 - A < p.re) (h2 : p.re < 1 / 2 + A) (h3 : -T < p.im) (h4 : p.im < T) :
    Rectangle (burnolRectLow A T) (burnolRectHigh A T) ∈ 𝓝 p := by
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  constructor
  · rw [burnolRectLow_re, burnolRectHigh_re, Set.uIoo_of_le (by linarith)]
    exact ⟨h1, h2⟩
  · rw [burnolRectLow_im, burnolRectHigh_im, Set.uIoo_of_le (by linarith)]
    exact ⟨h3, h4⟩

/-! ## The residue identity -/

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-- **Burnol's residue identity on one rectangle.**  Only `Z` and the nontrivial zeros of height
below `T` contribute: the residue at `Z` is `−M(f)(Z)`, and the points `0`, `1` and the trivial
zeros are regular points of the integrand. -/
theorem rectangleIntegral'_burnolIntegrand_extendedMellin (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {Z : ℂ} (hZζ : riemannZeta Z ≠ 0) (hZ1 : Z ≠ 1) (hZ0 : Z ≠ 0)
    {A T : ℝ} (hA : 1 ≤ A) (hT : 0 < T)
    (hAint : ∀ k : ℕ, (1 / 2 - A : ℝ) ≠ -(2 * ((k : ℝ) + 1)))
    (hZre1 : 1 / 2 - A < Z.re) (hZre2 : Z.re < 1 / 2 + A) (hZim : |Z.im| < T)
    (hTz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T) :
    RectangleIntegral' (burnolIntegrand (extendedMellinContinuation a c d f) Z)
        (burnolRectLow A T) (burnolRectHigh A T)
      = -extendedMellinContinuation a c d f Z
        + ∑ ρ ∈ nontrivialZeroFinset T,
            laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1) := by
  classical
  set G : ℂ → ℂ := extendedMellinContinuation a c d f with hGdef
  set z : ℂ := burnolRectLow A T with hzdef
  set w : ℂ := burnolRectHigh A T with hwdef
  have hzre : z.re = 1 / 2 - A := by rw [hzdef, burnolRectLow_re]
  have hzim : z.im = -T := by rw [hzdef, burnolRectLow_im]
  have hwre : w.re = 1 / 2 + A := by rw [hwdef, burnolRectHigh_re]
  have hwim : w.im = T := by rw [hwdef, burnolRectHigh_im]
  have hle_re : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have hle_im : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  -- membership in the rectangle
  have hmem : ∀ p : ℂ, p ∈ Rectangle z w ↔
      1 / 2 - A ≤ p.re ∧ p.re ≤ 1 / 2 + A ∧ -T ≤ p.im ∧ p.im ≤ T := by
    intro p
    rw [hzdef, hwdef]
    exact mem_burnolRect (by linarith) hT.le p
  have hnbhd_of : ∀ p : ℂ, 1 / 2 - A < p.re → p.re < 1 / 2 + A → -T < p.im → p.im < T →
      Rectangle z w ∈ 𝓝 p := by
    intro p h1 h2 h3 h4
    rw [hzdef, hwdef]
    exact burnolRect_mem_nhds h1 h2 h3 h4
  -- the analytic input
  have hGmero : ∀ s : ℂ, MeromorphicAt G s :=
    fun s => meromorphicAt_extendedMellinContinuation ha hev hc hd s
  have hGana : ∀ s ∈ Rectangle z w, s ∉ ({0} : Finset ℂ) → s ≠ 1 → AnalyticAt ℂ G s := by
    intro s _ hs0 hs1
    refine analyticAt_extendedMellinContinuation_of_ne ha hev hc hd ?_ hs1
    simpa using hs0
  -- every pole is interior
  have hnbhd : ∀ p ∈ burnolPoleSet z w Z ({0} : Finset ℂ), Rectangle z w ∈ 𝓝 p := by
    intro p hp
    rw [mem_burnolPoleSet] at hp
    rcases hp with rfl | rfl | hp0 | hpz
    · exact hnbhd_of _ hZre1 hZre2 (by simpa using (abs_lt.1 hZim).1) (abs_lt.1 hZim).2
    · refine hnbhd_of _ (by simp; linarith) (by simp; linarith) (by simp; linarith)
        (by simp; linarith)
    · have : p = 0 := by simpa using hp0
      subst this
      exact hnbhd_of _ (by simp; linarith) (by simp; linarith) (by simp; linarith)
        (by simp; linarith)
    · rw [mem_zetaZeroFinset] at hpz
      obtain ⟨hpr, hpzero⟩ := hpz
      rw [hmem] at hpr
      rcases riemannZeta_zero_trivial_or_mem_strip hpzero with ⟨n, hn⟩ | ⟨h1, h2⟩
      · have hre : p.re = -(2 * ((n : ℝ) + 1)) := by rw [hn]; simp
        have him : p.im = 0 := by rw [hn]; simp
        refine hnbhd_of _ ?_ ?_ (by rw [him]; linarith) (by rw [him]; linarith)
        · rcases lt_or_eq_of_le hpr.1 with h | h
          · exact h
          · exact absurd (by rw [← hre, ← h]) (hAint n)
        · rw [hre]
          have : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
          linarith
      · refine hnbhd_of _ (by linarith) (by linarith) ?_ ?_
        · have habs : |p.im| ≠ T := hTz p hpzero h1 h2
          rcases lt_or_eq_of_le hpr.2.2.2 with h | h
          · rcases lt_or_eq_of_le hpr.2.2.1 with h' | h'
            · exact h'
            · exact absurd (by rw [← h']; rw [abs_of_nonpos (by linarith)]; ring) habs
          · exact absurd (by rw [h, abs_of_nonneg (by linarith)]) habs
        · have habs : |p.im| ≠ T := hTz p hpzero h1 h2
          rcases lt_or_eq_of_le hpr.2.2.2 with h | h
          · exact h
          · exact absurd (by rw [h, abs_of_nonneg (by linarith)]) habs
  rw [rectangleIntegral'_burnolIntegrand hle_re hle_im hGmero hGana hnbhd]
  -- split off `Z`
  set P' : Finset ℂ := insert (1 : ℂ) (({0} : Finset ℂ) ∪ zetaZeroFinset z w) with hP'def
  have hZnot : Z ∉ P' := by
    rw [hP'def, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    push Not
    refine ⟨hZ1, hZ0, ?_⟩
    intro hcon
    exact hZζ (mem_zetaZeroFinset.1 hcon).2
  have hsplit : burnolPoleSet z w Z ({0} : Finset ℂ) = insert Z P' := rfl
  rw [hsplit, Finset.sum_insert hZnot]
  have hresZ : laurentCoeff (burnolIntegrand G Z) Z (-1) = -G Z := by
    refine laurentCoeff_burnolIntegrand_self ?_ hZζ hZ1
    exact analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hZ0 hZ1
  rw [hresZ]
  congr 1
  -- the remaining points: only the nontrivial zeros survive
  set q : ℂ → Prop := fun p => riemannZeta p = 0 ∧ 0 < p.re ∧ p.re < 1 with hqdef
  have hfilter : P'.filter q = nontrivialZeroFinset T := by
    ext ρ
    rw [Finset.mem_filter, mem_nontrivialZeroFinset]
    constructor
    · rintro ⟨hmemP, hzero, h1, h2⟩
      refine ⟨hzero, h1, h2, ?_⟩
      rw [hP'def, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hmemP
      rcases hmemP with rfl | h0 | hZF
      · simp at h2
      · have : ρ = 0 := by simpa using h0
        rw [this] at h1
        simp at h1
      · rw [mem_zetaZeroFinset, hmem] at hZF
        have habs : |ρ.im| ≠ T := hTz ρ hzero h1 h2
        rcases lt_or_eq_of_le hZF.1.2.2.2 with h | h
        · rcases lt_or_eq_of_le hZF.1.2.2.1 with h' | h'
          · rw [abs_lt]
            exact ⟨h', h⟩
          · exact absurd (by rw [← h', abs_of_nonpos (by linarith)]; ring) habs
        · exact absurd (by rw [h, abs_of_nonneg (by linarith)]) habs
    · rintro ⟨hzero, h1, h2, him⟩
      have hmemZF : ρ ∈ zetaZeroFinset z w := by
        refine mem_zetaZeroFinset.2 ⟨?_, hzero⟩
        rw [hmem]
        have habs := abs_lt.1 him
        exact ⟨by linarith, by linarith, habs.1.le, habs.2.le⟩
      refine ⟨?_, hzero, h1, h2⟩
      rw [hP'def, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr hmemZF)
  have hzeroSum : ∑ p ∈ P'.filter (fun p => ¬ q p), laurentCoeff (burnolIntegrand G Z) p (-1)
      = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hmemP, hnq⟩ := hp
    rw [hP'def, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hmemP
    rcases hmemP with rfl | h0 | hZF
    · exact laurentCoeff_burnolIntegrand_extendedMellin_one ha hev hc hd hZζ (Ne.symm hZ1)
    · have hp0 : p = 0 := by simpa using h0
      subst hp0
      exact laurentCoeff_burnolIntegrand_extendedMellin_zero ha hev hc hd hZζ (Ne.symm hZ0)
    · rw [mem_zetaZeroFinset] at hZF
      obtain ⟨-, hpzero⟩ := hZF
      rcases riemannZeta_zero_trivial_or_mem_strip hpzero with ⟨n, hn⟩ | ⟨h1, h2⟩
      · have hpe : p = -(2 * ((n + 1 : ℕ) : ℂ)) := by rw [hn]; push_cast; ring
        subst hpe
        refine laurentCoeff_burnolIntegrand_extendedMellin_trivial ha hev hc hd hZζ
          (Nat.succ_ne_zero n) ?_
        intro hcon
        rw [hcon] at hpzero
        exact hZζ hpzero
      · exact absurd ⟨hpzero, h1, h2⟩ hnq
  rw [← Finset.sum_filter_add_sum_filter_not P' q, hfilter, hzeroSum, add_zero]

end

end RHTower
