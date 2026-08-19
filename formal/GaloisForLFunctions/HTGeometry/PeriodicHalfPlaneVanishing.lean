import GaloisForLFunctions.HTGeometry.GammaMonomialAnalytic

/-!
# A periodic analytic function on a half plane that decays vertically vanishes

The orbit limit of a Gamma monomial is `1`-periodic and analytic on a right half plane, and tends to
its expected value as `|Im s| → ∞`.  This file proves that such a function is constant — and hence
equal to that value — by the maximum modulus principle applied on the half plane itself, using
periodicity only to move an arbitrary point into a fixed compact block.

No descent to `ℂ∖{0}` and no removable-singularity argument are needed: the supremum of `‖F‖` over
the half plane is attained on the compact block, hence at an interior point, so `F` is constant.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem periodic_shift_nat {R₀ : ℝ} {F : ℂ → ℂ}
    (hper : ∀ s : ℂ, R₀ < s.re → F (s + 1) = F s) :
    ∀ (n : ℕ) (s : ℂ), R₀ < s.re → F (s + (n : ℂ)) = F s := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro s hs
      have h1 : R₀ < (s + (n : ℂ)).re := by
        rw [Complex.add_re, Complex.natCast_re]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hcast : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
      rw [hcast, hper _ h1, ih s hs]

theorem periodic_shift_nat_sub {R₀ : ℝ} {F : ℂ → ℂ}
    (hper : ∀ s : ℂ, R₀ < s.re → F (s + 1) = F s) :
    ∀ (n : ℕ) (s : ℂ), R₀ + (n : ℝ) < s.re → F (s - (n : ℂ)) = F s := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro s hs
      have hs' : R₀ + (n : ℝ) < (s - 1).re := by
        rw [Complex.sub_re, Complex.one_re]
        push_cast at hs
        linarith
      have hs1 : R₀ < (s - 1).re := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hcast : s - ((n + 1 : ℕ) : ℂ) = (s - 1) - (n : ℂ) := by push_cast; ring
      have hback : F s = F (s - 1) := by
        have := hper (s - 1) hs1
        simpa using this
      rw [hcast, ih (s - 1) hs', hback]

/-- Every point of the half plane has a translate with the same value in a fixed vertical block. -/
theorem exists_block_translate {R₀ : ℝ} {F : ℂ → ℂ}
    (hper : ∀ s : ℂ, R₀ < s.re → F (s + 1) = F s) (s : ℂ) (hs : R₀ < s.re) :
    ∃ s₀ : ℂ, R₀ + 1 ≤ s₀.re ∧ s₀.re ≤ R₀ + 3 ∧ s₀.im = s.im ∧ F s₀ = F s := by
  classical
  set m : ℕ := ⌈R₀ + 2 - s.re⌉₊ with hm
  set s' : ℂ := s + (m : ℂ) with hs'
  have hs'im : s'.im = s.im := by rw [hs']; simp
  have hs're : s'.re = s.re + (m : ℝ) := by rw [hs']; simp
  have hmge : R₀ + 2 - s.re ≤ (m : ℝ) := Nat.le_ceil _
  have hs'ge : R₀ + 2 ≤ s'.re := by rw [hs're]; linarith
  have hs'H : R₀ < s'.re := by linarith
  have hFs' : F s' = F s := periodic_shift_nat hper m s hs
  set n : ℕ := ⌊s'.re - R₀ - 1⌋₊ with hn
  have hnle : (n : ℝ) ≤ s'.re - R₀ - 1 := by
    rw [hn]
    exact Nat.floor_le (by linarith)
  have hngt : s'.re - R₀ - 1 < (n : ℝ) + 1 := by
    rw [hn]
    exact Nat.lt_floor_add_one _
  refine ⟨s' - (n : ℂ), ?_, ?_, ?_, ?_⟩
  · rw [Complex.sub_re, Complex.natCast_re]
    linarith
  · rw [Complex.sub_re, Complex.natCast_re]
    linarith
  · rw [Complex.sub_im, Complex.natCast_im, hs'im]
    ring
  · rw [periodic_shift_nat_sub hper n s' (by linarith), hFs']


theorem isCompact_vertical_block (a b T : ℝ) :
    IsCompact {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ |s.im| ≤ T} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have h1 : IsClosed {s : ℂ | a ≤ s.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {s : ℂ | s.re ≤ b} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {s : ℂ | |s.im| ≤ T} :=
      isClosed_le (Complex.continuous_im.abs) continuous_const
    have hset : {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ |s.im| ≤ T}
        = {s : ℂ | a ≤ s.re} ∩ ({s : ℂ | s.re ≤ b} ∩ {s : ℂ | |s.im| ≤ T}) := by
      ext s; simp [Set.mem_inter_iff]
    rw [hset]
    exact h1.inter (h2.inter h3)
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨|a| + |b| + T, fun s hs => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hs
    have hre : |s.re| ≤ |a| + |b| := by
      rcases abs_cases s.re with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
          rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> linarith
    have hnorm := Complex.norm_le_abs_re_add_abs_im s
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith

/-- **A periodic analytic function on a half plane that decays vertically vanishes.** -/
theorem eq_zero_of_periodic_of_vertical_decay {R₀ : ℝ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s : ℂ | R₀ < s.re})
    (hper : ∀ s : ℂ, R₀ < s.re → F (s + 1) = F s)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ s : ℂ, R₀ < s.re → T ≤ |s.im| → ‖F s‖ ≤ ε) :
    ∀ s : ℂ, R₀ < s.re → F s = 0 := by
  classical
  intro s₁ hs₁
  by_contra hne
  have hpos : 0 < ‖F s₁‖ := norm_pos_iff.mpr hne
  set ε : ℝ := ‖F s₁‖ / 2 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨T, hT⟩ := hdecay ε hε0
  set T' : ℝ := max T 1 with hT'
  set H : Set ℂ := {s : ℂ | R₀ < s.re} with hH
  set K : Set ℂ := {s : ℂ | R₀ + 1 ≤ s.re ∧ s.re ≤ R₀ + 3 ∧ |s.im| ≤ T'} with hKdef
  have hKsub : K ⊆ H := by
    intro s hs
    exact lt_of_lt_of_le (by linarith) hs.1
  have hKcomp : IsCompact K := isCompact_vertical_block _ _ _
  -- the distinguished point lands in the block
  have hs₁im : |s₁.im| < T' := by
    by_contra hcon
    push Not at hcon
    have := hT s₁ hs₁ (le_trans (le_max_left _ _) hcon)
    rw [hε] at this
    linarith
  obtain ⟨z₁, hz₁a, hz₁b, hz₁im, hz₁F⟩ := exists_block_translate hper s₁ hs₁
  have hz₁K : z₁ ∈ K := ⟨hz₁a, hz₁b, by rw [hz₁im]; linarith⟩
  have hKne : K.Nonempty := ⟨z₁, hz₁K⟩
  obtain ⟨z, hzK, hzmax⟩ := hKcomp.exists_isMaxOn hKne
    ((hF.mono hKsub).continuousOn.norm)
  have hzbig : ε < ‖F z‖ := by
    have h1 : ‖F z₁‖ ≤ ‖F z‖ := hzmax hz₁K
    have h2 : ‖F s₁‖ ≤ ‖F z‖ := by rw [← hz₁F]; exact h1
    have hεv : ε = ‖F s₁‖ / 2 := hε
    linarith [hpos, h2, hεv]
  have hglobal : IsMaxOn (norm ∘ F) H z := by
    intro s hs
    by_cases him : T' ≤ |s.im|
    · have h1 := hT s hs (le_trans (le_max_left _ _) him)
      exact le_trans h1 (le_of_lt hzbig)
    · push Not at him
      obtain ⟨s₀, ha, hb, him0, hF0⟩ := exists_block_translate hper s hs
      have hs₀K : s₀ ∈ K := ⟨ha, hb, by rw [him0]; linarith⟩
      have hmem : ‖F s₀‖ ≤ ‖F z‖ := hzmax hs₀K
      have hgoal : ‖F s‖ ≤ ‖F z‖ := by rw [← hF0]; exact hmem
      exact hgoal
  have hopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected H := by
    have hconv : Convex ℝ H := convex_halfSpace_re_gt R₀
    exact hconv.isPreconnected
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hconn hopen hF (hKsub hzK) hglobal
  obtain ⟨T₂, hT₂⟩ := hdecay ε hε0
  set w : ℂ := (R₀ + 2 : ℝ) + ((max T₂ 1 : ℝ)) * Complex.I with hw
  have hwH : R₀ < w.re := by rw [hw]; simp
  have hwim : max T₂ 1 ≤ |w.im| := by
    rw [hw]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, Complex.ofReal_im, zero_add, mul_one, mul_zero, add_zero]
    rw [abs_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
  have hwsmall := hT₂ w hwH (le_trans (le_max_left _ _) hwim)
  have hwz : F w = F z := heq hwH
  rw [hwz] at hwsmall
  linarith

end

end GaloisForLFunctions.HTGeometry
