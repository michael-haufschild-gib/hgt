import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import GaloisForLFunctions.HTGeometry.ModularArcMinimumPrinciple

/-!
# A Neumann minimum principle for the stream operator on the modular half-strip

Let `R = {(u, y) : 0 ≤ u ≤ ½, u² + y² ≥ 1, y > 0}` be the right half of the standard fundamental
domain of `SL₂(ℤ)`, with the corner `P = (½, √3/2)`, and let

`L* χ = χ_uu + χ_yy − χ_y / y = y (∂_u (y⁻¹ χ_u) + ∂_y (y⁻¹ χ_y))`.

If `v` solves `div(y ∇v) = 0`, its stream function (`χ_u = y v_y`, `χ_y = −y v_u`) solves
`L* χ = 0`; if `v` is constant on the arc `u² + y² = 1`, the radial derivative of `χ` vanishes
there (Neumann condition), and `χ` restricted to the arc is the flux of `v` through the arc counted
from the point where `χ = 0`.

**Theorem** (`nonneg_of_neumann_on_modularHalfArc`).  Let `b > 0` with `b² > ¾`.  Suppose
* `L* χ = 0` at the interior points of `R` above height `b`;
* the radial derivative of `χ` from outside the unit disc vanishes on the open arc above height `b`;
* `χ ≥ 0` on the sides `u = 0` and `u = ½` above height `b`;
* `χ ≥ 0` at every point of `R` of height at most `b`, except the corner `P`;
* `χ ≥ −ε` above some height, for every `ε > 0` (uniformly in `u`);
* `χ` is continuous on `R ∩ {y ≥ b}`.

Then `χ ≥ 0` on `R ∖ {P}`.

Proof.  Suppose `χ(p₀) = −m < 0`.  Truncate at a height `Y` above which `χ ≥ −m/4`, and put
`g = χ − ε(u² + y²)` with `ε(¼ + Y²) = m/4`.  Since `L*(u² + y²) = 2`, and the radial derivative of
`u² + y²` on the unit circle is `2`, we get `L* g = −2ε < 0`, and the outward radial derivative of
`g` on the arc is `−2ε < 0`.  The minimum of `g` on the compact region `R ∩ {b ≤ y ≤ Y}` is
`≤ −m`.  It is not on the top, the bottom or the sides, where `g ≥ −m/2`.  It is not on the arc,
where the one-sided radial derivative into the region would be `≥ 0`.  It is not inside, where the
second-derivative test gives `L* g ≥ 0`.
-/

open Filter Topology Set

namespace GaloisForLFunctions
namespace HTGeometry

/-- The right half of the modular fundamental domain between the heights `b` and `Y`. -/
def halfArcRegion (b Y : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 / 2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧ b ≤ p.2 ∧ p.2 ≤ Y}

theorem isCompact_halfArcRegion (b Y : ℝ) : IsCompact (halfArcRegion b Y) := by
  have hsub : halfArcRegion b Y ⊆ Icc (0 : ℝ) (1 / 2) ×ˢ Icc b Y := by
    rintro p ⟨h1, h2, -, h4, h5⟩
    exact ⟨⟨h1, h2⟩, h4, h5⟩
  refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ hsub
  have heq : halfArcRegion b Y = {p : ℝ × ℝ | 0 ≤ p.1} ∩ {p | p.1 ≤ 1 / 2} ∩
      {p | 1 ≤ p.1 ^ 2 + p.2 ^ 2} ∩ {p | b ≤ p.2} ∩ {p | p.2 ≤ Y} := by
    ext p
    simp only [halfArcRegion, mem_inter_iff, mem_setOf_eq]
    tauto
  rw [heq]
  refine ((((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_)).inter
    (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_) <;> fun_prop

/-- **One-sided Fermat lemma.**  At a minimum from the right the right derivative is `≥ 0`. -/
theorem nonneg_of_isLocalMinOn_Ici {g : ℝ → ℝ} {g' : ℝ} (hmin : IsLocalMinOn g (Ici 0) 0)
    (hg : HasDerivWithinAt g g' (Ici 0) 0) : 0 ≤ g' := by
  have hy : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 :=
    mem_posTangentConeAt_of_segment_subset (by
      rw [zero_add, segment_eq_Icc zero_le_one]
      exact Icc_subset_Ici_self)
  simpa using hmin.hasFDerivWithinAt_nonneg hg.hasFDerivWithinAt hy

theorem hasDerivAt_const_mul_sq_add (ε c s : ℝ) :
    HasDerivAt (fun s => ε * (s ^ 2 + c)) (ε * (2 * s)) s :=
  (((hasDerivAt_pow 2 s).add_const c).const_mul ε).congr_deriv (by ring)

theorem hasDerivAt_const_mul_add_sq (ε c s : ℝ) :
    HasDerivAt (fun s => ε * (c + s ^ 2)) (ε * (2 * s)) s :=
  (((hasDerivAt_pow 2 s).const_add c).const_mul ε).congr_deriv (by ring)

theorem hasDerivAt_const_mul_two_mul (ε s : ℝ) :
    HasDerivAt (fun s => ε * (2 * s)) (ε * 2) s :=
  (((hasDerivAt_id s).const_mul 2).const_mul ε).congr_deriv (by simp)

/-- **Neumann minimum principle for the stream operator on the modular half-strip.** -/
theorem nonneg_of_neumann_on_modularHalfArc {χ χu χuu χy χyy : ℝ → ℝ → ℝ} {b : ℝ}
    (hb0 : 0 < b) (hb : 3 / 4 < b ^ 2)
    (hu : ∀ u y, 0 < u → u < 1 / 2 → 1 < u ^ 2 + y ^ 2 → b < y →
      HasDerivAt (fun s => χ s y) (χu u y) u)
    (huu : ∀ u y, 0 < u → u < 1 / 2 → 1 < u ^ 2 + y ^ 2 → b < y →
      HasDerivAt (fun s => χu s y) (χuu u y) u)
    (hy : ∀ u y, 0 < u → u < 1 / 2 → 1 < u ^ 2 + y ^ 2 → b < y →
      HasDerivAt (fun s => χ u s) (χy u y) y)
    (hyy : ∀ u y, 0 < u → u < 1 / 2 → 1 < u ^ 2 + y ^ 2 → b < y →
      HasDerivAt (fun s => χy u s) (χyy u y) y)
    (hL : ∀ u y, 0 < u → u < 1 / 2 → 1 < u ^ 2 + y ^ 2 → b < y →
      χuu u y + χyy u y - χy u y / y = 0)
    (harc : ∀ u y, 0 < u → u < 1 / 2 → b < y → u ^ 2 + y ^ 2 = 1 →
      HasDerivWithinAt (fun t => χ ((1 + t) * u) ((1 + t) * y)) 0 (Ici 0) 0)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => χ p.1 p.2)
      {p | 0 ≤ p.1 ∧ p.1 ≤ 1 / 2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧ b ≤ p.2})
    (hside0 : ∀ y, b ≤ y → 0 ≤ χ 0 y) (hside1 : ∀ y, b ≤ y → 0 ≤ χ (1 / 2) y)
    (hlow : ∀ u y, 0 ≤ u → u ≤ 1 / 2 → 1 ≤ u ^ 2 + y ^ 2 → 0 < y → 3 / 4 < y ^ 2 → y ≤ b →
      0 ≤ χ u y)
    (hcusp : ∀ ε > 0, ∃ Y, ∀ u y, 0 ≤ u → u ≤ 1 / 2 → Y ≤ y → -ε ≤ χ u y)
    {u₀ y₀ : ℝ} (hu₀ : 0 ≤ u₀) (hu₀' : u₀ ≤ 1 / 2) (h₀ : 1 ≤ u₀ ^ 2 + y₀ ^ 2) (hy₀ : 0 < y₀)
    (hy₀' : 3 / 4 < y₀ ^ 2) : 0 ≤ χ u₀ y₀ := by
  by_contra hneg
  rw [not_le] at hneg
  have hby₀ : b < y₀ := by
    by_contra h
    rw [not_lt] at h
    exact absurd (hlow u₀ y₀ hu₀ hu₀' h₀ hy₀ hy₀' h) (not_le.mpr hneg)
  set m := -χ u₀ y₀ with hm
  have hm0 : 0 < m := by linarith
  obtain ⟨Y₁, hY₁⟩ := hcusp (m / 4) (by linarith)
  set Y := max Y₁ (y₀ + 1) with hY
  have hYy₀ : y₀ < Y := by linarith [le_max_right Y₁ (y₀ + 1)]
  have hYtop : ∀ u, 0 ≤ u → u ≤ 1 / 2 → -(m / 4) ≤ χ u Y := fun u h1 h2 =>
    hY₁ u Y h1 h2 (le_max_left _ _)
  set C := 1 / 4 + Y ^ 2 with hC
  have hC0 : 0 < C := by positivity
  set ε := m / 4 / C with hε
  have hε0 : 0 < ε := by positivity
  set g : ℝ × ℝ → ℝ := fun p => χ p.1 p.2 - ε * (p.1 ^ 2 + p.2 ^ 2) with hg
  set K := halfArcRegion b Y with hK
  have hgw : ∀ p ∈ K, ε * (p.1 ^ 2 + p.2 ^ 2) ≤ m / 4 := by
    rintro p ⟨h1, h2, -, h4, h5⟩
    have hp2 : 0 ≤ p.2 := hb0.le.trans h4
    have hle : p.1 ^ 2 + p.2 ^ 2 ≤ C := by rw [hC]; nlinarith
    calc ε * (p.1 ^ 2 + p.2 ^ 2) ≤ ε * C := mul_le_mul_of_nonneg_left hle hε0.le
      _ = m / 4 := by rw [hε]; field_simp
  have hp₀K : (u₀, y₀) ∈ K := ⟨hu₀, hu₀', h₀, hby₀.le, hYy₀.le⟩
  have hgcont : ContinuousOn g K := by
    refine (hcont.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩).sub ?_
    exact (by fun_prop : Continuous fun p : ℝ × ℝ => ε * (p.1 ^ 2 + p.2 ^ 2)).continuousOn
  obtain ⟨q, hqK, hqmin⟩ := (isCompact_halfArcRegion b Y).exists_isMinOn ⟨_, hp₀K⟩ hgcont
  have hqmin' : ∀ p ∈ K, g q ≤ g p := fun p hp => hqmin hp
  have hgq : g q ≤ -m := by
    have h1 := hqmin' _ hp₀K
    have h2 : 0 ≤ ε * (u₀ ^ 2 + y₀ ^ 2) := by positivity
    simp only [hg] at h1 ⊢
    linarith
  have hgwq := hgw q hqK
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hqK
  have hq0 : 0 < q.2 := hb0.trans_le hq4
  have hχq : χ q.1 q.2 ≤ -(3 * m / 4) := by
    simp only [hg] at hgq
    linarith
  -- the minimizer is not on the top
  have hqY : q.2 < Y := by
    rcases hq5.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hYtop q.1 hq1 hq2
      rw [h] at hχq
      linarith
  -- not on the bottom
  have hqb : b < q.2 := by
    rcases hq4.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hlow q.1 q.2 hq1 hq2 hq3 hq0 (by rw [← h]; exact hb) h.ge
      linarith
  -- not on the sides
  have hq1' : 0 < q.1 := by
    rcases hq1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hside0 q.2 hq4
      rw [show q.1 = 0 from h.symm] at hχq
      linarith
  have hq2' : q.1 < 1 / 2 := by
    rcases hq2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hside1 q.2 hq4
      rw [h] at hχq
      linarith
  rcases hq3.lt_or_eq with hq3' | hq3'
  · -- interior point: the second-derivative test
    have hI : ∀ᶠ p in 𝓝 q, 0 < p.1 ∧ p.1 < 1 / 2 ∧ 1 < p.1 ^ 2 + p.2 ^ 2 ∧ b < p.2 ∧ p.2 < Y := by
      have c1 : ∀ᶠ p in 𝓝 q, 0 < p.1 :=
        continuousAt_const.eventually_lt continuous_fst.continuousAt hq1'
      have c2 : ∀ᶠ p in 𝓝 q, p.1 < 1 / 2 :=
        continuous_fst.continuousAt.eventually_lt continuousAt_const hq2'
      have c3 : ∀ᶠ p in 𝓝 q, 1 < p.1 ^ 2 + p.2 ^ 2 :=
        continuousAt_const.eventually_lt (by fun_prop) hq3'
      have c4 : ∀ᶠ p in 𝓝 q, b < p.2 :=
        continuousAt_const.eventually_lt continuous_snd.continuousAt hqb
      have c5 : ∀ᶠ p in 𝓝 q, p.2 < Y :=
        continuous_snd.continuousAt.eventually_lt continuousAt_const hqY
      filter_upwards [c1, c2, c3, c4, c5] with p h1 h2 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩
    have hlinU : Tendsto (fun s : ℝ => (s, q.2)) (𝓝 q.1) (𝓝 q) := by
      have : Continuous fun s : ℝ => (s, q.2) := by fun_prop
      simpa using this.tendsto q.1
    have hlinY : Tendsto (fun s : ℝ => (q.1, s)) (𝓝 q.2) (𝓝 q) := by
      have : Continuous fun s : ℝ => (q.1, s) := by fun_prop
      simpa using this.tendsto q.2
    have hIU := hlinU.eventually hI
    have hIY := hlinY.eventually hI
    have hminU : IsLocalMin (fun s => χ s q.2 - ε * (s ^ 2 + q.2 ^ 2)) q.1 :=
      hIU.mono fun s hs => by
        have := hqmin' (s, q.2) ⟨hs.1.le, hs.2.1.le, hs.2.2.1.le, hs.2.2.2.1.le, hs.2.2.2.2.le⟩
        simpa [hg] using this
    have hminY : IsLocalMin (fun s => χ q.1 s - ε * (q.1 ^ 2 + s ^ 2)) q.2 :=
      hIY.mono fun s hs => by
        have := hqmin' (q.1, s) ⟨hs.1.le, hs.2.1.le, hs.2.2.1.le, hs.2.2.2.1.le, hs.2.2.2.2.le⟩
        simpa [hg] using this
    have hUU : 0 ≤ χuu q.1 q.2 - ε * 2 :=
      nonneg_of_isLocalMin_of_hasDerivAt hminU
        (hIU.mono fun s hs => (hu s q.2 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1).sub
          (hasDerivAt_const_mul_sq_add ε (q.2 ^ 2) s))
        ((huu q.1 q.2 hq1' hq2' hq3' hqb).sub (hasDerivAt_const_mul_two_mul ε q.1))
    have hYY : 0 ≤ χyy q.1 q.2 - ε * 2 :=
      nonneg_of_isLocalMin_of_hasDerivAt hminY
        (hIY.mono fun s hs => (hy q.1 s hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1).sub
          (hasDerivAt_const_mul_add_sq ε (q.1 ^ 2) s))
        ((hyy q.1 q.2 hq1' hq2' hq3' hqb).sub (hasDerivAt_const_mul_two_mul ε q.2))
    have hY1 : χy q.1 q.2 - ε * (2 * q.2) = 0 :=
      hminY.hasDerivAt_eq_zero
        ((hy q.1 q.2 hq1' hq2' hq3' hqb).sub (hasDerivAt_const_mul_add_sq ε (q.1 ^ 2) q.2))
    have hdiv : χy q.1 q.2 / q.2 = 2 * ε := by
      rw [show χy q.1 q.2 = ε * (2 * q.2) by linarith]
      field_simp
    have hLq := hL q.1 q.2 hq1' hq2' hq3' hqb
    linarith
  · -- arc point: the one-sided radial derivative
    have hd := harc q.1 q.2 hq1' hq2' hqb hq3'.symm
    have hw : HasDerivWithinAt (fun t : ℝ => ε * (((1 + t) * q.1) ^ 2 + ((1 + t) * q.2) ^ 2))
        (2 * ε) (Ici 0) 0 := by
      have e : (fun t : ℝ => ε * (((1 + t) * q.1) ^ 2 + ((1 + t) * q.2) ^ 2)) =
          fun t => ε * (q.1 ^ 2 + q.2 ^ 2) * (1 + t) ^ 2 := by
        funext t
        ring
      rw [e]
      have h1 : HasDerivAt (fun t : ℝ => ε * (q.1 ^ 2 + q.2 ^ 2) * (1 + t) ^ 2)
          (ε * (q.1 ^ 2 + q.2 ^ 2) * (2 * (1 + 0) ^ 1 * 1)) 0 :=
        (((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).const_mul _ |>.congr_deriv (by simp)
      refine h1.hasDerivWithinAt.congr_deriv ?_
      rw [← hq3']
      ring
    have hmin : IsLocalMinOn (fun t : ℝ => χ ((1 + t) * q.1) ((1 + t) * q.2) -
        ε * (((1 + t) * q.1) ^ 2 + ((1 + t) * q.2) ^ 2)) (Ici 0) 0 := by
      have e1 : ∀ᶠ t in 𝓝 (0 : ℝ), (1 + t) * q.1 < 1 / 2 :=
        (by fun_prop : Continuous fun t : ℝ => (1 + t) * q.1).continuousAt.eventually_lt
          continuousAt_const (by simpa using hq2')
      have e2 : ∀ᶠ t in 𝓝 (0 : ℝ), (1 + t) * q.2 < Y :=
        (by fun_prop : Continuous fun t : ℝ => (1 + t) * q.2).continuousAt.eventually_lt
          continuousAt_const (by simpa using hqY)
      filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
        with t h1 h2 h3
      have ht : (0 : ℝ) ≤ t := h3
      have hsq : ((1 + t) * q.1) ^ 2 + ((1 + t) * q.2) ^ 2 = (1 + t) ^ 2 := by
        rw [show ((1 + t) * q.1) ^ 2 + ((1 + t) * q.2) ^ 2 = (1 + t) ^ 2 * (q.1 ^ 2 + q.2 ^ 2) by
          ring, ← hq3', mul_one]
      have hmem : ((1 + t) * q.1, (1 + t) * q.2) ∈ K := by
        refine ⟨mul_nonneg (by linarith) hq1, h1.le, ?_, ?_, h2.le⟩
        · simp only
          rw [hsq]
          nlinarith
        · simp only
          nlinarith [mul_nonneg ht hq0.le]
      have := hqmin' _ hmem
      simpa [hg] using this
    have h0 := nonneg_of_isLocalMinOn_Ici hmin (hd.sub hw)
    linarith

end HTGeometry
end GaloisForLFunctions
