import GaloisForLFunctions.RHTower.XiSymmetricDiscIndexParity
import GaloisForLFunctions.RHTower.GaussianFormationReflectedHermiteBiehler
import GaloisForLFunctions.HTGeometry.SlitPlaneQuotientDiscZeroFree

/-!
# A local certificate for the Riemann hypothesis on a symmetric disc, against a source model

Let `D = ball c t` be centred on the critical line.  Compare `ξ` with a model `G` holomorphic
near `D̄`, whose zeros in `D` are simple and lie on `Re s = ½`.  If `ξ/G` omits `(−∞, 0]` on
`∂D`, symmetric Rouché gives equal zero counts.  The off-line multiplicity of `ξ` in `D` is even
(reflection `ρ ↦ 1 − ρ̄`).  Hence, as soon as `ξ` has at least `#{zeros of G in D} − 1` distinct
zeros on the diameter, every zero of `ξ` in `D` lies on the critical line.

This is the TG sub-quantum gate on symmetric discs, with the integer supplied by a model
instead of by `ξ` itself: the winding comparison is a slit-plane condition on one circle and the
on-line count comes from sign changes of the real function `t ↦ ξ(½+it)`.

For the tilted reflected Gaussian formation `Ξₓ,λ` (`λ ≥ λₓ`), the model hypotheses hold at every
height, so the certificate reduces to the slit-plane comparison plus a sign count.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- `ξ` is real on the critical line. -/
theorem im_xi_criticalLine (τ : ℝ) : (xi (1 / 2 + τ * I)).im = 0 := by
  have hconj : (starRingEnd ℂ) (1 / 2 + (τ : ℂ) * I) = 1 - (1 / 2 + (τ : ℂ) * I) := by
    apply Complex.ext <;> (simp; try norm_num)
  have h := xi_conj (1 / 2 + (τ : ℂ) * I)
  rw [hconj, xi_one_sub] at h
  have him := congrArg Complex.im h
  rw [Complex.conj_im] at him
  linarith

/-- A sign change of `t ↦ ξ(½+it)` on `[a, b]` produces a critical-line zero in `(a, b)`. -/
theorem exists_xi_criticalLine_zero_of_sign_change {a b : ℝ} (hab : a < b)
    (hsign : (xi (1 / 2 + a * I)).re * (xi (1 / 2 + b * I)).re < 0) :
    ∃ τ ∈ Ioo a b, xi (1 / 2 + τ * I) = 0 := by
  set f : ℝ → ℝ := fun τ => (xi (1 / 2 + τ * I)).re with hf
  have hcont : Continuous f := by
    have : Continuous fun τ : ℝ => xi (1 / 2 + τ * I) :=
      xi_differentiable.continuous.comp (by fun_prop)
    exact Complex.continuous_re.comp this
  have hfa : f a ≠ 0 := by
    intro h; rw [hf] at h; simp only at h; rw [h, zero_mul] at hsign; exact lt_irrefl _ hsign
  have hfb : f b ≠ 0 := by
    intro h; rw [hf] at h; simp only at h; rw [h, mul_zero] at hsign; exact lt_irrefl _ hsign
  have hzero : ∃ τ ∈ Ioo a b, f τ = 0 := by
    rcases lt_or_gt_of_ne hfa with ha | ha
    · have hb : 0 < f b := by
        by_contra hb; push Not at hb
        have := mul_nonneg_of_nonpos_of_nonpos ha.le hb
        simp only [hf] at this; linarith
      obtain ⟨τ, hτ, h0⟩ := intermediate_value_Ioo hab.le hcont.continuousOn
        (show (0 : ℝ) ∈ Ioo (f a) (f b) from ⟨ha, hb⟩)
      exact ⟨τ, hτ, h0⟩
    · have hb : f b < 0 := by
        by_contra hb; push Not at hb
        have := mul_nonneg ha.le hb
        simp only [hf] at this; linarith
      obtain ⟨τ, hτ, h0⟩ := intermediate_value_Ioo' hab.le hcont.continuousOn
        (show (0 : ℝ) ∈ Ioo (f b) (f a) from ⟨hb, ha⟩)
      exact ⟨τ, hτ, h0⟩
  obtain ⟨τ, hτ, h0⟩ := hzero
  exact ⟨τ, hτ, Complex.ext (by simpa [hf] using h0) (by simpa using im_xi_criticalLine τ)⟩

/-- **Model certificate on a symmetric disc.**  Let `c` lie on the critical line and let `G` be
holomorphic on an open set containing `closedBall c R`, `t < R`, nonvanishing on `∂D`, with every
zero in `D = ball c t` simple and listed in `ZG`.  If `ξ/G` omits `(−∞, 0]` on `∂D` and `ξ` has a
set `W` of distinct critical-line zeros in `D` with `#ZG ≤ #W + 1`, then every zero of `ξ` in `D`
lies on the critical line. -/
theorem xi_onLine_of_model_certificate {c : ℂ} (hc : c.re = 1 / 2) {t R : ℝ} (ht : 0 < t)
    (htR : t < R) {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall c R ⊆ U) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G U) (hGs : ∀ ζ ∈ sphere c t, G ζ ≠ 0)
    (hslit : ∀ ζ ∈ sphere c t, xi ζ / G ζ ∈ slitPlane)
    (ZG : Finset ℂ) (hZGball : ∀ z ∈ ZG, z ∈ ball c t) (hZG : ∀ z ∈ ball c t, G z = 0 ↔ z ∈ ZG)
    (hGsimple : ∀ z ∈ ZG, zeroMult G z = 1)
    (W : Finset ℂ) (hW : ∀ z ∈ W, z ∈ ball c t ∧ z.re = 1 / 2 ∧ xi z = 0)
    (hcard : ZG.card ≤ W.card + 1) :
    ∀ z ∈ ball c t, xi z = 0 → z.re = 1 / 2 := by
  classical
  have hxiU : DifferentiableOn ℂ xi U := xi_differentiable.differentiableOn
  have hxis : ∀ ζ ∈ sphere c t, xi ζ ≠ 0 := fun ζ hζ h0 =>
    slitPlane_ne_zero (hslit ζ hζ) (by rw [h0, zero_div])
  have heq := zeroSumBall_eq_of_quotient_mem_slitPlane ht htR hU hsub hxiU hG hGs hslit
  obtain ⟨ZG', hZG'ball, hZG'zero, hZG'sum⟩ := exists_zeroSet_zeroSumBall ht htR hU hsub hG hGs
  have hZGZG' : ZG' = ZG := by
    ext z
    constructor
    · intro hz; exact (hZG z (hZG'ball z hz)).1 ((hZG'zero z (hZG'ball z hz)).2 hz)
    · intro hz; exact (hZG'zero z (hZGball z hz)).1 ((hZG z (hZGball z hz)).2 hz)
  obtain ⟨Z, hZball, hZzero, hZsum⟩ := exists_zeroSet_zeroSumBall ht htR hU hsub hxiU hxis
  have hZ1 : ∀ ρ ∈ Z, ρ ∈ ball c t ∧ xi ρ = 0 := fun ρ hρ =>
    ⟨hZball ρ hρ, (hZzero ρ (hZball ρ hρ)).2 hρ⟩
  have hZ2 : ∀ ρ ∈ ball c t, xi ρ = 0 → ρ ∈ Z := fun ρ hρ h0 => (hZzero ρ hρ).1 h0
  -- total multiplicity of `ξ` in `D` equals `#ZG`
  have htotal : (∑ ρ ∈ Z, (zeroMult xi ρ : ℤ)) = (ZG.card : ℤ) := by
    have h1 : (∑ ρ ∈ Z, (zeroMult xi ρ : ℂ)) = (ZG.card : ℂ) := by
      rw [← hZsum, heq, hZG'sum, hZGZG', Finset.sum_congr rfl
        (fun z hz => by rw [hGsimple z hz]), Finset.sum_const, nsmul_eq_mul]
      simp
    exact_mod_cast h1
  -- the on-line multiplicity is at least `#W`
  have hWsub : W ⊆ Z.filter (fun ρ => ρ.re = 1 / 2) := by
    intro z hz
    obtain ⟨hzb, hzre, hz0⟩ := hW z hz
    exact Finset.mem_filter.2 ⟨hZ2 z hzb hz0, hzre⟩
  have hon : (W.card : ℤ) ≤ ∑ ρ ∈ Z.filter (fun ρ => ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) := by
    calc (W.card : ℤ) = ∑ ρ ∈ W, (1 : ℤ) := by simp
      _ ≤ ∑ ρ ∈ W, (zeroMult xi ρ : ℤ) := Finset.sum_le_sum fun ρ hρ => by
          exact_mod_cast one_le_zeroMult_xi (hW ρ hρ).2.2
      _ ≤ ∑ ρ ∈ Z.filter (fun ρ => ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hWsub fun ρ _ _ => Int.natCast_nonneg _
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.re = 1 / 2)
    (fun ρ => (zeroMult xi ρ : ℤ))
  have hoff_le : ∑ ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) ≤ 1 := by
    have : ((ZG.card : ℕ) : ℤ) ≤ (W.card : ℤ) + 1 := by exact_mod_cast hcard
    linarith
  have heven := even_offLine_sum hc Z hZ1 hZ2
  have hnn : 0 ≤ ∑ ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) :=
    Finset.sum_nonneg fun ρ _ => Int.natCast_nonneg _
  have hoff0 : ∑ ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) = 0 := by
    obtain ⟨k, hk⟩ := heven
    omega
  intro z hz h0
  by_contra hre
  have hmem : z ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2) := Finset.mem_filter.2 ⟨hZ2 z hz h0, hre⟩
  have hone : (1 : ℤ) ≤ (zeroMult xi z : ℤ) := by exact_mod_cast one_le_zeroMult_xi h0
  have hle := Finset.single_le_sum (f := fun ρ => (zeroMult xi ρ : ℤ))
    (fun ρ _ => Int.natCast_nonneg _) hmem
  linarith

/-- The open critical strip. -/
def openCriticalStrip : Set ℂ := {w | 0 < w.re ∧ w.re < 1}

theorem isOpen_openCriticalStrip : IsOpen openCriticalStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- **Local TG certificate against the tilted Gaussian source.**  Let `c` lie on the critical line,
`closedBall c R` inside the open critical strip, `t < R`, `λ ≥ λₓ`, and put `G = Ξₓ,λ`.  If `G ≠ 0`
on `∂D` and `ξ/G` omits `(−∞, 0]` on `∂D`, then the zeros of `G` in `D` form a finite set `ZG` of
simple critical-line zeros, and any `#ZG − 1` distinct critical-line zeros of `ξ` in `D` force
every zero of `ξ` in `D` onto the critical line. -/
theorem xi_onLine_of_tiltedGaussianModel_certificate {x : ℝ} (hx : 0 < x) {l : ℝ}
    (hl : gaussianFormationTiltThreshold x ≤ l) {c : ℂ} (hc : c.re = 1 / 2) {t R : ℝ}
    (ht : 0 < t) (htR : t < R) (hsub : closedBall c R ⊆ openCriticalStrip)
    (hGs : ∀ ζ ∈ sphere c t, tiltedGaussianReflectedFormation x l ζ ≠ 0)
    (hslit : ∀ ζ ∈ sphere c t, xi ζ / tiltedGaussianReflectedFormation x l ζ ∈ slitPlane) :
    ∃ ZG : Finset ℂ,
      (∀ z ∈ ZG, z ∈ ball c t ∧ z.re = 1 / 2 ∧ tiltedGaussianReflectedFormation x l z = 0) ∧
      (∀ z ∈ ball c t, tiltedGaussianReflectedFormation x l z = 0 → z ∈ ZG) ∧
      ∀ W : Finset ℂ, (∀ z ∈ W, z ∈ ball c t ∧ z.re = 1 / 2 ∧ xi z = 0) →
        ZG.card ≤ W.card + 1 → ∀ z ∈ ball c t, xi z = 0 → z.re = 1 / 2 := by
  set G := tiltedGaussianReflectedFormation x l with hGdef
  have hd := tiltedGaussianFormation_differentiableAt hx l
  have hne := tiltedGaussianFormation_ne_zero x l
  have hcj := tiltedGaussianFormation_conj hx l
  have hpos : ∀ s : ℂ, 0 < s.re → (0 : ℝ) ≤ |s.im| →
      0 < (logDeriv (tiltedGaussianFormation x l) s).re :=
    fun _ hs _ => re_logDeriv_tiltedGaussianFormation_pos hx hl hs
  have hGU : DifferentiableOn ℂ G openCriticalStrip := fun w hw =>
    (ReflectionDominance.differentiableAt_reflected hd hw.1 hw.2).differentiableWithinAt
  obtain ⟨ZG, hZGball, hZGzero, -⟩ :=
    exists_zeroSet_zeroSumBall ht htR isOpen_openCriticalStrip hsub hGU hGs
  have hball_strip : ∀ z ∈ ball c t, z ∈ openCriticalStrip := fun z hz =>
    hsub (ball_subset_closedBall.trans (closedBall_subset_closedBall htR.le) hz)
  have hline : ∀ z ∈ ball c t, G z = 0 → z.re = 1 / 2 := by
    intro z hz h0
    by_contra hre
    obtain ⟨h0', h1'⟩ := hball_strip z hz
    exact ReflectionDominance.reflected_ne_zero hd hne hcj hpos h0' h1' hre (abs_nonneg _) h0
  have hsimple : ∀ z ∈ ZG, zeroMult G z = 1 := by
    intro z hz
    have hzb := hZGball z hz
    have h0 : G z = 0 := (hZGzero z hzb).2 hz
    have hre := hline z hzb h0
    have hzeq : z = 1 / 2 + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hre]
    have hderiv : deriv G z ≠ 0 := by
      rw [hzeq] at h0 ⊢
      exact ReflectionDominance.deriv_reflected_ne_zero_of_line hd hne hcj hpos
        (abs_nonneg _) h0
    obtain ⟨hz0, hz1⟩ := hball_strip z hzb
    have han : AnalyticAt ℂ G z :=
      hGU.analyticAt (isOpen_openCriticalStrip.mem_nhds ⟨hz0, hz1⟩)
    unfold zeroMult
    rw [han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 hderiv]
    rfl
  refine ⟨ZG, fun z hz => ⟨hZGball z hz, hline z (hZGball z hz) ((hZGzero z (hZGball z hz)).2 hz),
      (hZGzero z (hZGball z hz)).2 hz⟩, fun z hz h0 => (hZGzero z hz).1 h0, ?_⟩
  intro W hW hcard
  exact xi_onLine_of_model_certificate hc ht htR isOpen_openCriticalStrip hsub hGU hGs hslit ZG
    hZGball hZGzero hsimple W hW hcard

end

end RHTower
