import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WolffBlindnessRequiresSeparation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowerDefectCountsTheFrobeniusEigenvalues
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# One probe sees every outer eigenvalue

The weight `W_b(g) = Σ_{β(τ)=b} X_τ(g) conj X_{1−τ̄}(g)` of an outer Frobenius eigenvalue `b` can
vanish by cancellation inside its class: the zeros sharing the eigenvalue `b` at scale `ℓ`. For
the modulated bumps `g_s = φ e^{isu}` (`probe s 0`) the weight is
`W_b(s) = Σ_{β(τ)=b} m_τ Â(s + γ_τ)`, `A = φ ⋆ φ̃` (`frobWeight_probe_eq`), and the sum continues to
an entire function of `s` (`differentiable_probeClassWeight`). All zeros of a class have the same
real part `½ + δ`, so at `s = t + iδ` every argument `t + Im τ` is real, where `Â = |φ̂|² ≥ 0`:
the continued weight is a sum of nonnegative terms, positive for suitable `t`
(`exists_probeClassWeight_ne_zero`). Hence a class weight vanishes at only countably many real
modulations (`countable_badModulation`), for every tempered configuration and every class, finite
or infinite.

* **One probe sees everything** (`exists_probe_frobWeight_ne_zero`). Some modulation `s` makes
  every outer eigenvalue at every prime visible to `g_s`.
* **Fixed-test tower laws without weight hypotheses.** For that probe the tower at every prime
  carries exactly the distinct outer eigenvalues once the real parts of the right zeros are
  well-founded (`exists_probe_tower_law_of_wellFounded`; for finitely many right zeros this is
  `exists_test_tower_defect_eq_card_frobEig`), and sees every eigenvalue whose reciprocal is
  accessible from the origin off the folded spectrum (`exists_probe_card_le_towerDefect`).
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate Classical lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. The continued class weight -/

/-- The class weight of the probes, continued to complex modulations:
`W_b(s) = Σ_{β(τ) = b} m_τ Â(s + γ_τ)`, `A = φ ⋆ φ̃`. -/
def probeClassWeight (Z : ZeroConfig) (ℓ : ℝ) (b : ℂ) (s : ℂ) : ℂ :=
  ∑' τ : Z.carrier, if frobEig ℓ τ = b then (Z.mult τ : ℂ) * paperFT bumpAuto (s + gammaOf τ)
    else 0

/-- At real modulations the continued class weight is the weight of the probe. -/
theorem frobWeight_probe_eq (Z : ZeroConfig) (ℓ : ℝ) (b : ℂ) (s : ℝ) :
    frobWeight Z (probe s 0) ℓ b = probeClassWeight Z ℓ b s := by
  unfold frobWeight probeClassWeight
  refine tsum_congr fun τ => ?_
  split_ifs
  · rw [zeroCoord_mul_conj_reflect_probe, paperFT_mul_cexp]
  · rfl

/-- `1/(1 + |Re γ|)² ≤ (4/3)/(1 + |γ|²)` in the strip `|Im γ| ≤ ½`. -/
theorem inv_one_add_abs_re_sq_le {γ : ℂ} (h : |γ.im| ≤ 1 / 2) :
    1 / (1 + |γ.re|) ^ 2 ≤ (4 / 3) / (1 + Complex.normSq γ) := by
  rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
    (by nlinarith [mul_self_nonneg γ.re, mul_self_nonneg γ.im])]
  have h1 : γ.im * γ.im ≤ 1 / 4 := by nlinarith [abs_le.mp h]
  nlinarith [abs_nonneg γ.re, sq_abs γ.re]

/-- **A uniform bound on the probe terms.** The terms of the continued class weight are bounded by a
constant, depending on `‖s‖` only, times the tempered weights `m_τ/(1 + |γ_τ|²)`. -/
theorem exists_norm_probeTerm_le (Z : ZeroConfig) :
    ∃ a C : ℝ, 0 ≤ a ∧ 0 ≤ C ∧ ∀ (τ : Z.carrier) (s : ℂ),
      ‖(Z.mult τ : ℂ) * paperFT bumpAuto (s + gammaOf τ)‖ ≤
        Real.exp ((‖s‖ + 1 / 2) * a) * C * (1 + ‖s‖) ^ 2 * (4 / 3) *
          ((Z.mult τ : ℝ) / (1 + Complex.normSq (gammaOf τ))) := by
  obtain ⟨a, ha0, ha⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    bumpAuto_hasCompactSupport
  have hsupp : ∀ u, bumpAuto u ≠ 0 → |u| ≤ a := fun u hu => by
    by_contra h
    exact hu (ha u (not_le.mp h))
  set C : ℝ := 4 * ((∫ u, ‖bumpAuto u‖) + ∫ u, ‖deriv (deriv bumpAuto) u‖)
  have hC : 0 ≤ C := by
    have h1 : 0 ≤ ∫ u, ‖bumpAuto u‖ := MeasureTheory.integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv bumpAuto) u‖ :=
      MeasureTheory.integral_nonneg fun _ => norm_nonneg _
    positivity
  refine ⟨a, C, ha0, hC, fun τ s => ?_⟩
  set γ := gammaOf (τ : ℂ)
  set x := s + γ
  have hγim : |γ.im| ≤ 1 / 2 := abs_im_gammaOf_le Z τ
  have hdecay := RHTower.norm_paperFT_le_decay bumpAuto_contDiff hsupp x
  have hxim : |x.im| ≤ ‖s‖ + 1 / 2 := by
    have h1 : x.im = s.im + γ.im := Complex.add_im _ _
    rw [h1]
    exact (abs_add_le _ _).trans (add_le_add (Complex.abs_im_le_norm s) hγim)
  have hexp : Real.exp (|x.im| * a) ≤ Real.exp ((‖s‖ + 1 / 2) * a) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxim ha0)
  have hre : 1 + |γ.re| ≤ (1 + |x.re|) * (1 + ‖s‖) := by
    have h1 : γ.re = x.re - s.re := by simp [x]
    have h2 : |γ.re| ≤ |x.re| + ‖s‖ := by
      rw [h1]
      exact (abs_sub _ _).trans (add_le_add le_rfl (Complex.abs_re_le_norm s))
    nlinarith [abs_nonneg x.re, norm_nonneg s]
  have hden : 1 / (1 + |x.re|) ^ 2 ≤ (1 + ‖s‖) ^ 2 * ((4 / 3) / (1 + Complex.normSq γ)) := by
    have hp : 0 < 1 + |x.re| := by positivity
    have hq : 0 < 1 + |γ.re| := by positivity
    have h1 : 1 / (1 + |x.re|) ^ 2 ≤ (1 + ‖s‖) ^ 2 / (1 + |γ.re|) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (1 + |γ.re|) ^ 2 ≤ ((1 + |x.re|) * (1 + ‖s‖)) ^ 2 :=
            pow_le_pow_left₀ hq.le hre 2
        _ = (1 + ‖s‖) ^ 2 * (1 + |x.re|) ^ 2 := by ring
    refine h1.trans ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (inv_one_add_abs_re_sq_le hγim) (by positivity)
  have hm : (0 : ℝ) ≤ Z.mult τ := Nat.cast_nonneg _
  rw [norm_mul, Complex.norm_natCast]
  calc (Z.mult τ : ℝ) * ‖paperFT bumpAuto x‖
      ≤ (Z.mult τ : ℝ) * (Real.exp ((‖s‖ + 1 / 2) * a) * C * (1 / (1 + |x.re|) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (hdecay.trans ?_) hm
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hC) (by positivity)
    _ ≤ (Z.mult τ : ℝ) * (Real.exp ((‖s‖ + 1 / 2) * a) * C *
          ((1 + ‖s‖) ^ 2 * ((4 / 3) / (1 + Complex.normSq γ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden (by positivity)) hm
    _ = Real.exp ((‖s‖ + 1 / 2) * a) * C * (1 + ‖s‖) ^ 2 * (4 / 3) *
          ((Z.mult τ : ℝ) / (1 + Complex.normSq γ)) := by ring

/-- **The continued class weight is entire.** -/
theorem differentiable_probeClassWeight (Z : ZeroConfig) (hZ : TemperedConfig Z) (ℓ : ℝ)
    (b : ℂ) : Differentiable ℂ (probeClassWeight Z ℓ b) := by
  obtain ⟨a, C, ha0, hC, hbound⟩ := exists_norm_probeTerm_le Z
  intro s₀
  set R : ℝ := ‖s₀‖ + 1
  have hball : ∀ (τ : Z.carrier) (s : ℂ), s ∈ ball s₀ 1 →
      ‖(if frobEig ℓ τ = b then (Z.mult τ : ℂ) * paperFT bumpAuto (s + gammaOf τ) else 0)‖ ≤
        Real.exp ((R + 1 / 2) * a) * C * (1 + R) ^ 2 * (4 / 3) *
          ((Z.mult τ : ℝ) / (1 + Complex.normSq (gammaOf τ))) := by
    intro τ s hs
    have hsR : ‖s‖ ≤ R := by
      have := norm_le_norm_add_norm_sub' s s₀
      rw [mem_ball, dist_eq_norm] at hs
      simp only [R]
      linarith
    have hw : 0 ≤ (Z.mult τ : ℝ) / (1 + Complex.normSq (gammaOf τ)) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith [Complex.normSq_nonneg (gammaOf (τ : ℂ))])
    split_ifs
    · refine (hbound τ s).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (by linarith) ha0)) hC)
          (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by positivity) (by positivity))
        (by norm_num)) hw)
    · rw [norm_zero]
      exact mul_nonneg (by positivity) hw
  have hterm : ∀ τ : Z.carrier, DifferentiableOn ℂ (fun s => if frobEig ℓ τ = b then
      (Z.mult τ : ℂ) * paperFT bumpAuto (s + gammaOf τ) else 0) (ball s₀ 1) := by
    intro τ
    by_cases h : frobEig ℓ τ = b
    · simp only [h, if_true]
      exact ((RHTower.EvenSector.differentiable_paperFT_of_compact bumpAuto_contDiff.continuous
        bumpAuto_hasCompactSupport).comp (differentiable_id.add_const _)).const_mul _
        |>.differentiableOn
    · simp only [h, if_false]
      exact differentiableOn_const _
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm (hZ.mul_left _) hterm
    isOpen_ball hball
  exact (hdiff s₀ (mem_ball_self one_pos)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self one_pos))

/-- **The continued class weight does not vanish identically.** At `s = t + iδ`, `½ + δ` the common
real part of the class, every argument is real and the weight is `Σ m_τ |φ̂(t + Im τ)|² > 0` for
suitable `t`. -/
theorem exists_probeClassWeight_ne_zero (Z : ZeroConfig) (hZ : TemperedConfig Z) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {b : ℂ} (hb : b ∈ outerEig Z ℓ) : ∃ s : ℂ, probeClassWeight Z ℓ b s ≠ 0 := by
  obtain ⟨ρ, hρ, rfl⟩ := hb
  have hc : Continuous bump0 := (bumpTest_contDiff _ 0).continuous
  have hcs : HasCompactSupport bump0 := bumpTest_hasCompactSupport _ 0
  -- the bump has a nonzero transform somewhere on the real line
  obtain ⟨t₀, ht₀⟩ : ∃ t : ℝ, paperFT bump0 t ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∀ u, bump0 u = 0 := eq_zero_of_paperFT_real_eq_zero hc hcs h
    apply bumpAuto_zero_ne_zero
    rw [bumpAuto, RHTower.weilTest_apply]
    simp only [h0, zero_mul, MeasureTheory.integral_zero]
  set t : ℝ := t₀ - ρ.im
  set s : ℂ := (t : ℂ) + (ρ.re - 1 / 2 : ℝ) * I
  refine ⟨s, ?_⟩
  set r : Z.carrier → ℝ := fun τ => if frobEig ℓ τ = frobEig ℓ ρ then
    (Z.mult τ : ℝ) * Complex.normSq (paperFT bump0 ((t + (τ : ℂ).im : ℝ) : ℂ)) else 0
  -- on the class every argument is real and `Â = |φ̂|²`
  have hterm : ∀ τ : Z.carrier, (if frobEig ℓ τ = frobEig ℓ ρ then
      (Z.mult τ : ℂ) * paperFT bumpAuto (s + gammaOf τ) else 0) = ((r τ : ℝ) : ℂ) := by
    intro τ
    simp only [r]
    split_ifs with h
    · have hre : (τ : ℂ).re = ρ.re := re_eq_of_norm_frobEig_eq hℓ (by rw [h])
      have harg : s + gammaOf τ = ((t + (τ : ℂ).im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [s, gammaOf, hre]
      rw [harg, bumpAuto, EF.paperFT_weilTest hc hc hcs hcs, Complex.conj_ofReal,
        Complex.mul_conj]
      push_cast
      ring
    · simp
  have hr0 : ∀ τ, 0 ≤ r τ := fun τ => by
    simp only [r]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
    · exact le_rfl
  obtain ⟨a, C, ha0, hC, hbound⟩ := exists_norm_probeTerm_le Z
  have hrs : Summable r := by
    refine Summable.of_nonneg_of_le hr0 (fun τ => ?_) (hZ.mul_left
      (Real.exp ((‖s‖ + 1 / 2) * a) * C * (1 + ‖s‖) ^ 2 * (4 / 3)))
    have h := hterm τ
    split_ifs at h with hτ
    · have hn : r τ = ‖(Z.mult τ : ℂ) * paperFT bumpAuto (s + gammaOf τ)‖ := by
        rw [h, Complex.norm_real, Real.norm_of_nonneg (hr0 τ)]
      rw [hn]
      exact hbound τ s
    · have : r τ = 0 := by exact_mod_cast h.symm
      rw [this]
      exact mul_nonneg (by positivity)
        (div_nonneg (Nat.cast_nonneg _) (by linarith [Complex.normSq_nonneg (gammaOf (τ : ℂ))]))
  have hρpos : 0 < r ⟨ρ, hρ.1⟩ := by
    have hm : (0 : ℝ) < Z.mult ρ := Nat.cast_pos.mpr (Z.one_le_mult _ hρ.1)
    have ht : t + ρ.im = t₀ := by simp [t]
    show 0 < (if frobEig ℓ ρ = frobEig ℓ ρ then
      (Z.mult ρ : ℝ) * Complex.normSq (paperFT bump0 ((t + ρ.im : ℝ) : ℂ)) else 0)
    rw [if_pos rfl, ht]
    exact mul_pos hm (Complex.normSq_pos.mpr ht₀)
  have hsum : probeClassWeight Z ℓ (frobEig ℓ ρ) s = ((∑' τ, r τ : ℝ) : ℂ) := by
    rw [probeClassWeight, Complex.ofReal_tsum]
    exact tsum_congr hterm
  rw [hsum, Complex.ofReal_ne_zero]
  exact (lt_of_lt_of_le hρpos (hrs.le_tsum _ fun τ _ => hr0 τ)).ne'

/-- **Countably many bad modulations.** For every outer eigenvalue the weight of the probe `g_s`
vanishes at only countably many real `s`. -/
theorem countable_badModulation (Z : ZeroConfig) (hZ : TemperedConfig Z) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : ℂ} (hb : b ∈ outerEig Z ℓ) :
    {s : ℝ | frobWeight Z (probe s 0) ℓ b = 0}.Countable := by
  obtain ⟨s₀, hs₀⟩ := exists_probeClassWeight_ne_zero Z hZ hℓ hb
  refine ((countable_zeros_of_entire_nonzero (differentiable_probeClassWeight Z hZ ℓ b)
    hs₀).preimage Complex.ofReal_injective).mono fun s hs => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hs ⊢
  rwa [← frobWeight_probe_eq]

/-! ### 2. One probe for every prime -/

/-- **One probe sees every outer eigenvalue at every prime.** For every tempered configuration some
modulation `s` gives every outer eigenvalue `p^{ρ−½}`, at every prime `p`, a nonzero weight for
the probe `g_s`. -/
theorem exists_probe_frobWeight_ne_zero (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    ∃ s : ℝ, ∀ p : ℕ, p.Prime → ∀ b ∈ outerEig Z (Real.log p),
      frobWeight Z (probe s 0) (Real.log p) b ≠ 0 := by
  set B : Set ℝ := ⋃ p ∈ {p : ℕ | p.Prime}, ⋃ b ∈ outerEig Z (Real.log p),
    {s : ℝ | frobWeight Z (probe s 0) (Real.log p) b = 0}
  have hR : (rightZeros Z).Countable :=
    (SquareRootThreshold.countable_carrier Z).mono fun _ h => h.1
  have hB : B.Countable := by
    refine (Set.to_countable _).biUnion fun p hp => ?_
    have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast (show p.Prime from hp).one_lt)
    exact (hR.image _).biUnion fun b hb => countable_badModulation Z hZ hℓ hb
  obtain ⟨s, hs⟩ : ∃ s, s ∉ B := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real (hB.mono fun s _ => h s)
  refine ⟨s, fun p hp b hb h0 => hs ?_⟩
  exact Set.mem_biUnion (show p ∈ {p : ℕ | p.Prime} from hp) (Set.mem_biUnion hb h0)

/-- **The tower law for one probe at every prime, well-founded case.** If the real parts of the
right zeros contain no strictly increasing sequence, one probe `g` satisfies, at every prime `p`:
some window of the `p`-tower of `g` has `n` negative squares iff there are at least `n` distinct
outer eigenvalues `p^{ρ−½}`. -/
theorem exists_probe_tower_law_of_wellFounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hWF : (Complex.re '' rightZeros Z).WellFoundedOn (· > ·)) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g (Real.log p) K)) ↔
        (n : ℕ∞) ≤ (outerEig Z (Real.log p)).encard := by
  obtain ⟨s, hs⟩ := exists_probe_frobWeight_ne_zero Z hZ
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun p hp n => ?_⟩
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hvis : visibleSet Z (probe s 0) (Real.log p) = outerEig Z (Real.log p) :=
    Set.ext fun b => ⟨fun hb => hb.1, fun hb => ⟨hb, hs p hp b hb⟩⟩
  rw [tower_pontryagin_law_of_wellFounded Z hZ (probe_contDiff s 0) (probe_hasCompactSupport s 0)
    hℓ hWF n, hvis]

/-- **One probe sees every accessible eigenvalue at every prime.** For the probe of
`exists_probe_frobWeight_ne_zero`, at every prime, finitely many outer eigenvalues whose
reciprocals are accessible from the origin off its closed active folded spectrum are seen by one
window of its tower. -/
theorem exists_probe_card_le_towerDefect (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime →
      ∀ O : Finset ℂ, (∀ b ∈ O, b ∈ outerEig Z (Real.log p)) →
      (∀ b ∈ O, AccessibleOff (closure (activeFoldedSpectrum Z g (Real.log p))) b⁻¹) →
      ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g (Real.log p) K) := by
  obtain ⟨s, hs⟩ := exists_probe_frobWeight_ne_zero Z hZ
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun p hp O hO hacc => ?_⟩
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  exact card_le_towerDefect_of_accessibleOff Z hZ (probe_contDiff s 0)
    (probe_hasCompactSupport s 0) hℓ O (fun b hb => ⟨hO b hb, hs p hp b (hO b hb)⟩) hacc

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
