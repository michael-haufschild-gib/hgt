import GaloisForLFunctions.RHTower.EntireMinimumModulus
import GaloisForLFunctions.HTGeometry.PolyaConnectedTransfer
import GaloisForLFunctions.HTGeometry.CircleFloorMaxSelection
import GaloisForLFunctions.HTGeometry.ClunieSeparationBridge

/-!
# Composition growth by the minimum modulus

The minimum modulus of an analytic function with zeros is bounded below on some circle of every
sufficiently long radius window, with the zero count as the only loss.  Combined with the fact that a
continuous function on a ball attains every intermediate modulus, this bounds the composition from
below: whatever the inner function does, the composition reaches the outer function's floor.

This is the quantitative content of the composition growth principle in a form that needs neither a
displacement floor for the inner function nor a normalisation at the origin.
-/

open Complex Metric Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Composition growth from the minimum modulus.**  If the inner function `g` runs from modulus at
most `A` at the origin to modulus at least `B` somewhere on a ball, and the outer function `f` is
analytic with the stated boundary bound, then the composition attains the minimum-modulus floor
`H ^ n * L` on that ball, where `n` is the number of zeros of `f` in the inner disc. -/
theorem exists_le_norm_comp_of_analytic {f g : ℂ → ℂ} {U : Set ℂ} {R R' Mf H A B ρ : ℝ} {z₁ : ℂ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hMf : ∀ z : ℂ, ‖z‖ = R' → ‖f z‖ ≤ Mf)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R)
    (hρ : 0 ≤ ρ) (hg : ContinuousOn g (closedBall (0 : ℂ) ρ))
    (hz₁ : z₁ ∈ closedBall (0 : ℂ) ρ)
    (hgA : ‖g 0‖ ≤ A) (hgB : B ≤ ‖g z₁‖) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (0 < Mf → f 0 ≠ 0 →
        ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mf / ‖f 0‖)) ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        ∃ z ∈ closedBall (0 : ℂ) ρ, H ^ (∑ a ∈ T, m a) * L ≤ ‖f (g z)‖) := by
  obtain ⟨T, m, L, hL, hcount, hcircle⟩ :=
    exists_radius_norm_ge_of_analytic (A := A) hU hR h2R hball hf hnz hMf hH hB0 hBR
  refine ⟨T, m, L, hL, hcount, ?_⟩
  intro hgap
  obtain ⟨t, htmem, htfloor⟩ := hcircle hgap
  obtain ⟨htA, htB⟩ := Set.mem_Icc.mp htmem
  exact exists_le_norm_comp_of_floor hρ hg hz₁
    (Set.mem_Icc.mpr ⟨le_trans hgA htA, le_trans htB hgB⟩) htfloor

/-- **Pointwise separation of a composition from its inner state.**  Under the hypotheses above,
if the minimum-modulus floor of the outer function beats a prescribed multiple of the bound on the
inner function, then the composition outgrows that multiple of the inner state somewhere on the
ball. -/
theorem exists_posLog_separation_of_analytic {f g : ℂ → ℂ} {U : Set ℂ}
    {R R' Mf H A B ρ Mg C : ℝ} {z₁ : ℂ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hMf : ∀ z : ℂ, ‖z‖ = R' → ‖f z‖ ≤ Mf)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R)
    (hρ : 0 ≤ ρ) (hg : ContinuousOn g (closedBall (0 : ℂ) ρ))
    (hz₁ : z₁ ∈ closedBall (0 : ℂ) ρ)
    (hgA : ‖g 0‖ ≤ A) (hgB : B ≤ ‖g z₁‖)
    (hMg : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖g z‖ ≤ Mg) (hC : 0 ≤ C) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (0 < Mf → f 0 ≠ 0 →
        ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mf / ‖f 0‖)) ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        C * Real.posLog Mg < Real.posLog (H ^ (∑ a ∈ T, m a) * L) →
        ∃ z ∈ closedBall (0 : ℂ) ρ,
          C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖) := by
  obtain ⟨T, m, L, hL, hcount, hcircle⟩ :=
    exists_radius_norm_ge_of_analytic (A := A) hU hR h2R hball hf hnz hMf hH hB0 hBR
  refine ⟨T, m, L, hL, hcount, ?_⟩
  intro hgap hsep
  obtain ⟨t, htmem, htfloor⟩ := hcircle hgap
  obtain ⟨htA, htB⟩ := Set.mem_Icc.mp htmem
  have hfloor0 : 0 ≤ H ^ (∑ a ∈ T, m a) * L := by positivity
  exact exists_posLog_separation_of_closedBall hρ hg hz₁
    (Set.mem_Icc.mpr ⟨le_trans hgA htA, le_trans htB hgB⟩) htfloor hfloor0 hMg hC hsep

/-- **Simultaneous circle floor and composition growth.**  The minimum modulus supplies a circle on
which the auxiliary function `G` is bounded below; the circle is connected, so the inner function `g`
attains on it every modulus between its values there, and in particular the radius `t` at which the
outer function `f` has its own floor.  Both bounds therefore hold at a single point. -/
theorem exists_point_circle_floor_and_comp_of_analytic
    {G f g : ℂ → ℂ} {U : Set ℂ} {R R' MG H A B t L : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hG : AnalyticOnNhd ℂ G U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, G z = 0)
    (hMG : ∀ z : ℂ, ‖z‖ = R' → ‖G z‖ ≤ MG)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R)
    (hg : Continuous g)
    (hlow : ∀ σ ∈ Set.Icc A B, ∃ z₀ ∈ sphere (0 : ℂ) σ, ‖g z₀‖ ≤ t)
    (hhigh : ∀ σ ∈ Set.Icc A B, ∃ z₁ ∈ sphere (0 : ℂ) σ, t ≤ ‖g z₁‖)
    (hL : ∀ w : ℂ, ‖w‖ = t → L ≤ ‖f w‖) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (Lg : ℝ), 0 < Lg ∧
      (0 < MG → G 0 ≠ 0 →
        ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (MG / ‖G 0‖)) ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        ∃ z : ℂ, A ≤ ‖z‖ ∧ ‖z‖ ≤ B ∧
          H ^ (∑ a ∈ T, m a) * Lg ≤ ‖G z‖ ∧ L ≤ ‖f (g z)‖) := by
  obtain ⟨T, m, Lg, hLg, hcount, hcircle⟩ :=
    exists_radius_norm_ge_of_analytic (A := A) hU hR h2R hball hG hnz hMG hH hB0 hBR
  refine ⟨T, m, Lg, hLg, hcount, ?_⟩
  intro hgap
  obtain ⟨σ, hσmem, hσfloor⟩ := hcircle hgap
  have hGsphere : ∀ z ∈ sphere (0 : ℂ) σ, H ^ (∑ a ∈ T, m a) * Lg ≤ ‖G z‖ := by
    intro z hz
    exact hσfloor z (by simpa [mem_sphere_iff_norm] using hz)
  obtain ⟨z, hzmem, hzG, hzf⟩ :=
    exists_point_sphere_floor_and_comp (f := f) (g := g) (G := G)
      hg.continuousOn (hlow σ hσmem) (hhigh σ hσmem) hL hGsphere
  have hznorm : ‖z‖ = σ := by simpa [mem_sphere_iff_norm] using hzmem
  obtain ⟨hσA, hσB⟩ := Set.mem_Icc.mp hσmem
  exact ⟨z, by rw [hznorm]; exact hσA, by rw [hznorm]; exact hσB, hzG, hzf⟩

/-- **A separated point for the Clunie induction.**  The circle floor for the top grouped
coefficient `G` and the composition floor for `f ∘ g` are produced at one point, and the numeric
separation inequality is transported from the floor `L` to the value `‖f (g z)‖`.  This is exactly
the datum `separatesLast_of_pointwise` consumes, with `c := H ^ n * Lg`. -/
theorem exists_clunie_separated_point
    {G f g : ℂ → ℂ} {U : Set ℂ} {R R' MG H A B t L W : ℝ} {N NS : ℕ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hG : AnalyticOnNhd ℂ G U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, G z = 0)
    (hMG : ∀ z : ℂ, ‖z‖ = R' → ‖G z‖ ≤ MG)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R)
    (hg : Continuous g)
    (hlow : ∀ σ ∈ Set.Icc A B, ∃ z₀ ∈ sphere (0 : ℂ) σ, ‖g z₀‖ ≤ t)
    (hhigh : ∀ σ ∈ Set.Icc A B, ∃ z₁ ∈ sphere (0 : ℂ) σ, t ≤ ‖g z₁‖)
    (hL : ∀ w : ℂ, ‖w‖ = t → L ≤ ‖f w‖) (hL0 : 0 ≤ L) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (Lg : ℝ), 0 < Lg ∧
      (0 < MG → G 0 ≠ 0 →
        ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (MG / ‖G 0‖)) ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        W + (N : ℝ) * Real.posLog (1 / (H ^ (∑ a ∈ T, m a) * Lg))
            + ((N : ℝ) * (NS : ℝ) + (N : ℝ)) * Real.log 2 < Real.posLog L →
        ∃ z : ℂ, A ≤ ‖z‖ ∧ ‖z‖ ≤ B ∧
          0 < H ^ (∑ a ∈ T, m a) * Lg ∧
          H ^ (∑ a ∈ T, m a) * Lg ≤ ‖G z‖ ∧
          W + (N : ℝ) * Real.posLog (1 / (H ^ (∑ a ∈ T, m a) * Lg))
              + ((N : ℝ) * (NS : ℝ) + (N : ℝ)) * Real.log 2
            < Real.posLog ‖f (g z)‖) := by
  obtain ⟨T, m, Lg, hLg, hcount, hpoint⟩ :=
    exists_point_circle_floor_and_comp_of_analytic (t := t) (L := L)
      hU hR h2R hball hG hnz hMG hH hB0 hBR hg hlow hhigh hL
  refine ⟨T, m, Lg, hLg, hcount, ?_⟩
  intro hgap hsep
  obtain ⟨z, hzA, hzB, hzG, hzf⟩ := hpoint hgap
  have hfloorpos : 0 < H ^ (∑ a ∈ T, m a) * Lg := by positivity
  exact ⟨z, hzA, hzB, hfloorpos, hzG,
    lt_of_lt_of_le hsep (Real.posLog_le_posLog hL0 hzf)⟩

/-! ## A floor for the auxiliary function and the maximum term at one point -/

/-- **The selection the Clunie separation consumes.**  The minimum modulus supplies a circle on which
the auxiliary function `G` is bounded below everywhere; on that circle the maximum of `|f|` dominates
the maximum term.  Both hold at a single point, with no compatibility condition, because the floor is
uniform on the circle. -/
theorem exists_radius_floor_and_maxTerm {G : ℂ → ℂ} {a : ℕ → ℂ} {U : Set ℂ}
    {R R' MG H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hG : AnalyticOnNhd ℂ G U) (hnz : ∀ b ∈ U, ¬ ∀ᶠ z in 𝓝 b, G z = 0)
    (hMG : ∀ z : ℂ, ‖z‖ = R' → ‖G z‖ ≤ MG)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R) (hA : 0 < A)
    (ha : EntireCoeffs a) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (0 < MG → G 0 ≠ 0 →
        ((∑ b ∈ T, m b : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (MG / ‖G 0‖)) ∧
      (2 * ((∑ b ∈ T, m b : ℕ) : ℝ) * H < B - A →
        ∃ (s : ℝ) (z : ℂ), s ∈ Set.Icc A B ∧ ‖z‖ = s ∧
          H ^ (∑ b ∈ T, m b) * L ≤ ‖G z‖ ∧ maxTerm a s ≤ ‖coeffFun a z‖) := by
  obtain ⟨T, m, L, hL, hcount, hcircle⟩ :=
    exists_radius_norm_ge_of_analytic (A := A) hU hR h2R hball hG hnz hMG hH hB0 hBR
  refine ⟨T, m, L, hL, hcount, ?_⟩
  intro hgap
  obtain ⟨s, hs, hfloor⟩ := hcircle hgap
  obtain ⟨hsA, hsB⟩ := Set.mem_Icc.mp hs
  have hs0 : 0 < s := lt_of_lt_of_le hA hsA
  obtain ⟨z, hznorm, hGz, hmax⟩ := exists_point_norm_floor_and_maxTerm hs0 ha hfloor
  exact ⟨s, z, hs, hznorm, hGz, hmax⟩

/-! ## Floor, maximum term and block bound at one point -/

/-- **The three constants at one point.**  The minimum modulus supplies a circle carrying a floor for
the top grouped coefficient; the maximum of the dependent state on that circle dominates its maximum
term; and the sup bounds over the disc give the coefficient-and-earlier-state block there.

This produces `c₀` and `W` of `separatesLast_of_modulus_bound` simultaneously; only the modulus bound
for the dependent state is left to the composition growth. -/
theorem exists_radius_floor_maxTerm_block {G : ℂ → ℂ} {a : ℕ → ℂ} {U : Set ℂ} {k : ℕ}
    {R R' MG H A B α β D : ℝ}
    {S : Finset (Fin (k + 1) → ℕ)} {Apoly : (Fin (k + 1) → ℕ) → Polynomial ℂ}
    {F : Fin (k + 1) → ℂ → ℂ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hG : AnalyticOnNhd ℂ G U) (hnz : ∀ b ∈ U, ¬ ∀ᶠ z in 𝓝 b, G z = 0)
    (hMG : ∀ z : ℂ, ‖z‖ = R' → ‖G z‖ ≤ MG)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R) (hA : 0 < A)
    (ha : EntireCoeffs a)
    (hAsup : ∀ e ∈ S, ∀ w : ℂ, ‖w‖ ≤ B → Real.posLog ‖(Apoly e).eval w‖ ≤ α)
    (hFsup : ∀ i ∈ Finset.univ.erase (Fin.last k), ∀ w : ℂ, ‖w‖ ≤ B →
      Real.posLog ‖F i w‖ ≤ β)
    (hβ : 0 ≤ β)
    (hD : ∀ e ∈ S, ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) ≤ D) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (2 * ((∑ b ∈ T, m b : ℕ) : ℝ) * H < B - A →
        ∃ (s : ℝ) (z : ℂ), s ∈ Set.Icc A B ∧ ‖z‖ = s ∧
          H ^ (∑ b ∈ T, m b) * L ≤ ‖G z‖ ∧ maxTerm a s ≤ ‖coeffFun a z‖ ∧
          (∑ e ∈ S, (Real.posLog ‖(Apoly e).eval z‖
            + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖))
            ≤ (S.card : ℝ) * (α + D * β)) := by
  obtain ⟨T, m, L, hL, _, hpoint⟩ :=
    exists_radius_floor_and_maxTerm hU hR h2R hball hG hnz hMG hH hB0 hBR hA ha
  refine ⟨T, m, L, hL, ?_⟩
  intro hgap
  obtain ⟨s, z, hs, hznorm, hGz, hmax⟩ := hpoint hgap
  refine ⟨s, z, hs, hznorm, hGz, hmax, ?_⟩
  have hzB : ‖z‖ ≤ B := by
    rw [hznorm]
    exact (Set.mem_Icc.mp hs).2
  exact clunie_block_le_of_sup hzB hAsup hFsup hβ hD

end RHTower
