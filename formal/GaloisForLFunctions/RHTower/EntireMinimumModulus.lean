import GaloisForLFunctions.RHTower.MinimumModulus
import GaloisForLFunctions.HTGeometry.PolynomialMinimumModulus
import GaloisForLFunctions.HTGeometry.CompositionImageCircle
import GaloisForLFunctions.HTGeometry.PolyaMaximumTransfer

/-!
# The minimum modulus of an analytic function with zeros

Combining the zero extraction with the Borel--Carathéodory lower bound for the zero-free cofactor:
an analytic function that is nowhere locally zero is bounded below on some circle in any range of
radii long enough to avoid the moduli of its zeros.

The two halves are the cofactor package `exists_zero_free_cofactor_bounds` — analytic, zero-free on
the inner ball, bounded above there — and `norm_lower_bound_of_anchor`, which converts a supremum and
an anchor value into a floor for a zero-free function.  The polynomial part is handled by the circle
selection, which avoids the zeros by a measure argument.
-/

open Complex Metric Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Minimum modulus with zeros.**  For `R < R'` with the closed ball of radius `R'` inside the
domain, an analytic nowhere-locally-zero `f` bounded by `Mf` on the outer circle admits, for every
range `[A, B]` inside the inner ball that is long enough for the number of zeros, a circle on which
`‖f‖` is at least `H` to the total multiplicity times an explicit positive floor. -/
theorem exists_radius_norm_ge_of_analytic {f : ℂ → ℂ} {U : Set ℂ} {R R' Mf H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hMf : ∀ z : ℂ, ‖z‖ = R' → ‖f z‖ ≤ Mf)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (0 < Mf → f 0 ≠ 0 →
        ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mf / ‖f 0‖)) ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z‖ = s → H ^ (∑ a ∈ T, m a) * L ≤ ‖f z‖) := by
  classical
  have hRR' : R < R' := by linarith
  obtain ⟨T, m, g, hg, hTnorm, hgfree, hgsup, hfac⟩ :=
    exists_zero_free_cofactor_bounds hU hR hRR' hball hf hnz hMf
  -- the cofactor on the inner ball
  have hballR : closedBall (0 : ℂ) R ⊆ U :=
    subset_trans (closedBall_subset_closedBall (le_of_lt hRR')) hball
  have hgball : AnalyticOnNhd ℂ g (ball (0 : ℂ) R) :=
    hg.mono (subset_trans ball_subset_closedBall hballR)
  have hgne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0 := by
    intro z hz
    exact hgfree z (ball_subset_closedBall hz)
  set M : ℝ := Mf / (R' - R) ^ (∑ a ∈ T, m a) + 1 with hMdef
  have hgsup' : ∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ ≤ R' := by
      have := mem_ball.mp hz
      rw [dist_eq_norm, sub_zero] at this
      linarith
    have := hgsup z hzn
    rw [hMdef]
    linarith
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_eq_norm] using hR
  have hg0 : g 0 ≠ 0 := hgne 0 h0mem
  have hg0pos : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hg0M : ‖g 0‖ < M := by
    have hR'0 : (0 : ℝ) ≤ R' := by linarith
    have h := hgsup 0 (by simpa using hR'0)
    rw [hMdef]
    linarith
  have hlow := norm_lower_bound_of_anchor hB0 hBR hgball hgne hgsup' hg0pos hg0M (le_refl ‖g 0‖)
  set L : ℝ := ‖g 0‖ * Real.exp (-(2 * Real.log (M / ‖g 0‖) * B / (R - B))) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    positivity
  have h0U : (0 : ℂ) ∈ U := by
    refine hball ?_
    simp only [mem_closedBall, dist_eq_norm, sub_zero, norm_zero]
    linarith
  have hcount : 0 < Mf → f 0 ≠ 0 →
      ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mf / ‖f 0‖) := by
    intro hMf0 hf0
    refine sum_multiplicity_mul_log_le hR h2R hMf0 hTnorm ?_ (hfac 0 h0U) hf0
    refine hgsup 0 ?_
    simp only [norm_zero]
    linarith
  refine ⟨T, m, L, hLpos, hcount, ?_⟩
  intro hrange
  -- the polynomial part
  set P : Polynomial ℂ := ∏ a ∈ T, (Polynomial.X - Polynomial.C a) ^ (m a) with hPdef
  have hPmonic : P.Monic := by
    rw [hPdef]
    refine Polynomial.monic_prod_of_monic _ _ ?_
    intro a _
    exact (Polynomial.monic_X_sub_C a).pow _
  have hPdeg : P.natDegree = ∑ a ∈ T, m a := by
    rw [hPdef]
    exact natDegree_prod_X_sub_C_pow T m
  have hPeval : ∀ z : ℂ, P.eval z = ∏ a ∈ T, (z - a) ^ (m a) := by
    intro z
    rw [hPdef, Polynomial.eval_prod]
    refine Finset.prod_congr rfl ?_
    intro a _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hfacP : ∀ z : ℂ, ‖z‖ ≤ B → f z = P.eval z * g z := by
    intro z hz
    have hzU : z ∈ U := by
      refine hballR ?_
      simp only [mem_closedBall, dist_eq_norm, sub_zero]
      linarith
    rw [hPeval z]
    exact hfac z hzU
  have hglowB : ∀ z : ℂ, ‖z‖ ≤ B → L ≤ ‖g z‖ := by
    intro z hz
    refine hlow z ?_
    simp only [mem_closedBall, dist_eq_norm, sub_zero]
    exact hz
  have hrange' : 2 * (P.natDegree : ℝ) * H < B - A := by
    rw [hPdeg]
    exact hrange
  obtain ⟨s, hs, hbig⟩ :=
    exists_radius_norm_ge_of_factorization hPmonic hH (le_of_lt hLpos) hrange' hfacP hglowB
  refine ⟨s, hs, ?_⟩
  intro z hz
  have := hbig z hz
  rw [hPdeg] at this
  exact this

/-- **The minimum modulus with the zero count eliminated.**  On a good circle the logarithm of `‖f‖`
is at least `log L` minus the growth ratio `log(Mf/‖f 0‖)` divided by `log((R'−R)/R)`, times
`−log H`.  No quantity in the statement refers to the zeros. -/
theorem exists_radius_log_norm_ge_of_analytic {f : ℂ → ℂ} {U : Set ℂ} {R R' Mf H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hMf : ∀ z : ℂ, ‖z‖ = R' → ‖f z‖ ≤ Mf) (hMf0 : 0 < Mf) (hf0 : f 0 ≠ 0)
    (hH : 0 < H) (hH1 : H ≤ 1) (hB0 : 0 ≤ B) (hBR : B < R)
    (hrange : 2 * (Real.log (Mf / ‖f 0‖) / Real.log ((R' - R) / R)) * H < B - A) :
    ∃ L : ℝ, 0 < L ∧ ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z‖ = s →
      Real.log L + (Real.log (Mf / ‖f 0‖) / Real.log ((R' - R) / R)) * Real.log H
        ≤ Real.log ‖f z‖ := by
  obtain ⟨T, m, L, hLpos, hcount', hmain⟩ :=
    exists_radius_norm_ge_of_analytic hU hR h2R hball hf hnz hMf hH hB0 hBR
  have hcount := hcount' hMf0 hf0
  have hD : 0 < Real.log ((R' - R) / R) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hR]
    linarith
  have hNle : ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ Real.log (Mf / ‖f 0‖) / Real.log ((R' - R) / R) := by
    rw [le_div_iff₀ hD]
    exact hcount
  have hrange' : 2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A := by
    nlinarith [hNle, hH]
  obtain ⟨s, hs, hbig⟩ := hmain hrange'
  refine ⟨L, hLpos, s, hs, ?_⟩
  intro z hz
  have hpos : 0 < H ^ (∑ a ∈ T, m a) * L := by positivity
  have hlog := Real.log_le_log hpos (hbig z hz)
  have hloss := log_pow_mul_ge_of_count (N := ∑ a ∈ T, m a) hH hH1 hLpos hD hcount
  linarith

/-- **The circle floor and the composition separation, in one statement.**  The minimum-modulus
theorem selects a circle and a floor `Λ` for `log ‖f‖` on it; if the inner function reaches that
circle and its size is small enough against the floor, the composition separates pointwise. -/
theorem exists_circle_floor_and_separation {f g : ℂ → ℂ} {U : Set ℂ}
    {R R' Mf H A B r Mg C : ℝ} {z₀ : ℂ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hMf : ∀ z : ℂ, ‖z‖ = R' → ‖f z‖ ≤ Mf) (hMf0 : 0 < Mf) (hf0 : f 0 ≠ 0)
    (hH : 0 < H) (hH1 : H ≤ 1) (hB0 : 0 ≤ B) (hBR : B < R)
    (hrange : 2 * (Real.log (Mf / ‖f 0‖) / Real.log ((R' - R) / R)) * H < B - A)
    (hcont : ContinuousOn g (closedBall (0 : ℂ) r)) (hz₀ : z₀ ∈ closedBall (0 : ℂ) r)
    (hgz : g 0 = 0) (hMgb : ∀ z ∈ closedBall (0 : ℂ) r, ‖g z‖ ≤ Mg) (hC : 0 ≤ C) :
    ∃ (Λ s : ℝ), s ∈ Set.Icc A B ∧ (∀ w : ℂ, ‖w‖ = s → Λ ≤ Real.log ‖f w‖) ∧
      (0 ≤ s → s ≤ ‖g z₀‖ → C * Real.posLog Mg < Λ →
        ∃ z ∈ closedBall (0 : ℂ) r,
          C * Real.posLog ‖g z‖ < Real.posLog ‖f (g z)‖) := by
  obtain ⟨L, hLpos, s, hs, hfloor⟩ :=
    exists_radius_log_norm_ge_of_analytic hU hR h2R hball hf hnz hMf hMf0 hf0 hH hH1 hB0 hBR hrange
  refine ⟨Real.log L + (Real.log (Mf / ‖f 0‖) / Real.log ((R' - R) / R)) * Real.log H, s, hs,
    hfloor, ?_⟩
  intro hs0 hsg hsep
  exact GaloisForLFunctions.HTGeometry.exists_posLog_separation_of_log_floor hcont hz₀ hgz hs0 hsg
    hfloor hMgb hC hsep

/-- **Composition growth from the minimum modulus of the inner function.**  The minimum-modulus
theorem applied to `g − g 0` selects a circle on which the inner displacement is at least
`H ^ (∑ m) · L`; the composition inequality then bounds the outer function on a disc of half that
radius about `g 0` by any bound for `f ∘ g` on the disc.

Everything on the right refers to the outer function's *maximum*, so a transcendental outer function
makes the composition large. -/
theorem exists_radius_composition_bound {g : ℂ → ℂ} {U : Set ℂ} {R R' Mg H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, g z - g 0 = 0)
    (hMg : ∀ z : ℂ, ‖z‖ = R' → ‖g z - g 0‖ ≤ Mg)
    (hH : 0 < H) (hA : 0 < A) (hAB : A ≤ B) (hBR : B < R) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        ∃ s ∈ Set.Icc A B, ∀ (f : ℂ → ℂ) (ρ K : ℝ), 0 < ρ →
          ρ < H ^ (∑ a ∈ T, m a) * L / 2 →
          AnalyticOnNhd ℂ f (closedBall (g 0) ρ) →
          (∀ z ∈ closedBall (0 : ℂ) s, ‖f (g z)‖ ≤ K) →
          ∀ w ∈ closedBall (g 0) ρ, ‖f w‖ ≤ K) := by
  have hshift : AnalyticOnNhd ℂ (fun z => g z - g 0) U := hg.sub analyticOnNhd_const
  obtain ⟨T, m, L, hLpos, -, hmain⟩ :=
    exists_radius_norm_ge_of_analytic hU hR h2R hball hshift hnz hMg hH (le_of_lt (lt_of_lt_of_le hA hAB)) hBR
  refine ⟨T, m, L, hLpos, ?_⟩
  intro hrange
  obtain ⟨s, hs, hbig⟩ := hmain hrange
  refine ⟨s, hs, ?_⟩
  intro f ρ K hρ hρε hf hK
  have hspos : 0 < s := lt_of_lt_of_le hA hs.1
  have hballs : closedBall (0 : ℂ) s ⊆ U := by
    refine subset_trans (closedBall_subset_closedBall ?_) hball
    have := hs.2
    linarith
  have hgs : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) s) := hg.mono hballs
  have hfloor : ∀ z : ℂ, ‖z‖ = s → H ^ (∑ a ∈ T, m a) * L ≤ ‖g z - g 0‖ := hbig
  have h0U : (0 : ℂ) ∈ U := by
    refine hball ?_
    simp only [mem_closedBall, dist_eq_norm, sub_zero, norm_zero]
    linarith
  have hnc : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), g z = g 0 := by
    intro hcon
    refine hnz 0 h0U ?_
    filter_upwards [hcon] with z hz
    rw [hz, sub_self]
  exact norm_le_of_circle_floor hspos hρ hρε hgs hfloor hnc hf hK

/-- **A floor for the displacement.**  Factoring `g − g 0 = z^n G` and applying the minimum modulus
to `G` — which does not vanish at the origin, so the counting bound is available for it — gives a
circle on which the displacement itself is bounded below.  The factor `z^n` only helps, since the
radius is at least one. -/
theorem exists_radius_norm_sub_ge {g : ℂ → ℂ} {U : Set ℂ} {R R' Mg H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, g z - g 0 = 0)
    (hMg : ∀ z : ℂ, ‖z‖ = R' → ‖g z - g 0‖ ≤ Mg)
    (hH : 0 < H) (hA : 1 ≤ A) (hAB : A ≤ B) (hBR : B < R) :
    ∃ (n N : ℕ) (c L : ℝ), 0 < c ∧ 0 < L ∧
      (0 < Mg → (N : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mg / (R' ^ n * c))) ∧
      (2 * (N : ℝ) * H < B - A →
        ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z‖ = s → H ^ N * L ≤ ‖g z - g 0‖) := by
  have hR'pos : 0 < R' := by linarith
  have h0U : (0 : ℂ) ∈ U := by
    refine hball ?_
    simp only [mem_closedBall, dist_eq_norm, sub_zero, norm_zero]
    linarith
  have hnc : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), g z = g 0 := by
    intro hcon
    refine hnz 0 h0U ?_
    filter_upwards [hcon] with z hz
    rw [hz, sub_self]
  obtain ⟨n, G, hG, hG0, hfac⟩ :=
    GaloisForLFunctions.HTGeometry.exists_pow_factor_sub_const h0U hg hnc
  have hnzG : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, G z = 0 := by
    intro a ha
    refine GaloisForLFunctions.HTGeometry.not_eventually_zero_of_global_factor hU
      (a := 0) (n := n) ?_ ha (hnz a ha)
    intro z hz
    simpa using hfac z hz
  have hMG : ∀ z : ℂ, ‖z‖ = R' → ‖G z‖ ≤ Mg / R' ^ n := by
    intro z hz
    have hzU : z ∈ U := by
      refine hball ?_
      simp only [mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_eq hz
    have hnorm : ‖g z - g 0‖ = R' ^ n * ‖G z‖ := by
      rw [hfac z hzU, norm_mul, norm_pow, hz]
    have hpow : (0 : ℝ) < R' ^ n := by positivity
    rw [le_div_iff₀ hpow]
    have := hMg z hz
    rw [hnorm] at this
    linarith
  obtain ⟨T, m, L, hLpos, hcount, hmain⟩ :=
    exists_radius_norm_ge_of_analytic hU hR h2R hball hG hnzG hMG hH
      (by linarith : (0 : ℝ) ≤ B) hBR
  have hG0pos : 0 < ‖G 0‖ := norm_pos_iff.mpr hG0
  refine ⟨n, ∑ a ∈ T, m a, ‖G 0‖, L, hG0pos, hLpos, ?_, ?_⟩
  · intro hMg0
    have hMGpos : 0 < Mg / R' ^ n := by positivity
    have hbase := hcount hMGpos hG0
    have hrw : Mg / R' ^ n / ‖G 0‖ = Mg / (R' ^ n * ‖G 0‖) := by
      rw [div_div]
    rwa [hrw] at hbase
  intro hrange
  obtain ⟨s, hs, hbig⟩ := hmain hrange
  refine ⟨s, hs, ?_⟩
  intro z hz
  have hs1 : (1 : ℝ) ≤ s := le_trans hA hs.1
  have hzU : z ∈ U := by
    refine hball ?_
    simp only [mem_closedBall, dist_eq_norm, sub_zero, hz]
    linarith [hs.2]
  have hnorm : ‖g z - g 0‖ = s ^ n * ‖G z‖ := by
    rw [hfac z hzU, norm_mul, norm_pow, hz]
  have hGz := hbig z hz
  have hsn : (1 : ℝ) ≤ s ^ n := one_le_pow₀ hs1
  have hGnn : (0 : ℝ) ≤ ‖G z‖ := norm_nonneg _
  rw [hnorm]
  nlinarith [hGz, hsn, hGnn]

/-- **Composition growth with the zero count controlled.**  The displacement floor of
`exists_radius_norm_sub_ge` feeds the composition inequality: on the selected circle every outer
function analytic on the disc of radius `ρ < H^N L / 2` about `g 0` is bounded there by any bound for
`f ∘ g` on the source disc.  Unlike the earlier version, `N` is the zero count of the factor `G`,
which the counting bound controls. -/
theorem exists_radius_composition_bound_of_count {g : ℂ → ℂ} {U : Set ℂ} {R R' Mg H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, g z - g 0 = 0)
    (hMg : ∀ z : ℂ, ‖z‖ = R' → ‖g z - g 0‖ ≤ Mg)
    (hH : 0 < H) (hA : 1 ≤ A) (hAB : A ≤ B) (hBR : B < R) :
    ∃ (N : ℕ) (L : ℝ), 0 < L ∧
      (2 * (N : ℝ) * H < B - A →
        ∃ s ∈ Set.Icc A B, ∀ (f : ℂ → ℂ) (ρ K : ℝ), 0 < ρ → ρ < H ^ N * L / 2 →
          AnalyticOnNhd ℂ f (closedBall (g 0) ρ) →
          (∀ z ∈ closedBall (0 : ℂ) s, ‖f (g z)‖ ≤ K) →
          ∀ w ∈ closedBall (g 0) ρ, ‖f w‖ ≤ K) := by
  obtain ⟨-, N, -, L, -, hLpos, -, hmain⟩ :=
    exists_radius_norm_sub_ge hU hR h2R hball hg hnz hMg hH hA hAB hBR
  refine ⟨N, L, hLpos, ?_⟩
  intro hrange
  obtain ⟨s, hs, hfloor⟩ := hmain hrange
  refine ⟨s, hs, ?_⟩
  intro f ρ K hρ hρε hf hK
  have hspos : 0 < s := lt_of_lt_of_le (by linarith) hs.1
  have hballs : closedBall (0 : ℂ) s ⊆ U := by
    refine subset_trans (closedBall_subset_closedBall ?_) hball
    have := hs.2
    linarith
  have hgs : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) s) := hg.mono hballs
  have h0U : (0 : ℂ) ∈ U := by
    refine hball ?_
    simp only [mem_closedBall, dist_eq_norm, sub_zero, norm_zero]
    linarith
  have hnc : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), g z = g 0 := by
    intro hcon
    refine hnz 0 h0U ?_
    filter_upwards [hcon] with z hz
    rw [hz, sub_self]
  exact norm_le_of_circle_floor hspos hρ hρε hgs hfloor hnc hf hK

/-- **The displacement floor in logarithmic form.**  The zero count is folded into the growth ratio,
so the floor is stated with no reference to the number of zeros:

  `log L + (log(Mg/(R'^n c)) / log((R'−R)/R)) · log H  ≤  log ‖g z − g 0‖`

on a circle in `[A,B]`, provided the range is long enough for that same ratio. -/
theorem exists_radius_log_norm_sub_ge {g : ℂ → ℂ} {U : Set ℂ} {R R' Mg H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall (0 : ℂ) R' ⊆ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, g z - g 0 = 0)
    (hMg : ∀ z : ℂ, ‖z‖ = R' → ‖g z - g 0‖ ≤ Mg) (hMg0 : 0 < Mg)
    (hH : 0 < H) (hH1 : H ≤ 1) (hA : 1 ≤ A) (hAB : A ≤ B) (hBR : B < R) :
    ∃ (n : ℕ) (c L : ℝ), 0 < c ∧ 0 < L ∧
      (2 * (Real.log (Mg / (R' ^ n * c)) / Real.log ((R' - R) / R)) * H < B - A →
        ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z‖ = s →
          Real.log L
              + (Real.log (Mg / (R' ^ n * c)) / Real.log ((R' - R) / R)) * Real.log H
            ≤ Real.log ‖g z - g 0‖) := by
  obtain ⟨n, N, c, L, hcpos, hLpos, hcount, hmain⟩ :=
    exists_radius_norm_sub_ge hU hR h2R hball hg hnz hMg hH hA hAB hBR
  refine ⟨n, c, L, hcpos, hLpos, ?_⟩
  intro hrange
  have hD : 0 < Real.log ((R' - R) / R) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hR]
    linarith
  have hNle : (N : ℝ) ≤ Real.log (Mg / (R' ^ n * c)) / Real.log ((R' - R) / R) := by
    rw [le_div_iff₀ hD]
    exact hcount hMg0
  have hrange' : 2 * (N : ℝ) * H < B - A := by
    nlinarith [hNle, hH]
  obtain ⟨s, hs, hbig⟩ := hmain hrange'
  refine ⟨s, hs, ?_⟩
  intro z hz
  have hpos : 0 < H ^ N * L := by positivity
  have hlog := Real.log_le_log hpos (hbig z hz)
  have hloss :=
    GaloisForLFunctions.HTGeometry.log_pow_mul_ge_of_count (N := N) hH hH1 hLpos hD (hcount hMg0)
  linarith

end RHTower
