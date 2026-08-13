import Mathlib
import GaloisForLFunctions.Bottcher.HarmonicMinPrinciple
import GaloisForLFunctions.Bottcher.HarmonicMaxPrinciple

/-!
# Cone fullness of the configuration moves at the critical locus

For a finite family of spectral tests `F i` — holomorphic on a strip neighborhood of the
critical line, symmetric under `s ↦ 1−s` and `s ↦ s̄`, vanishing at infinity in the strip,
with line restrictions linearly independent — the three families of configuration moves

* insert a line pair at ordinate `β` (value `2·Re Fᵢ(1/2+iβ)`),
* delete a support line pair at ordinate `α` (value `−2·Re Fᵢ(1/2+iα)`),
* insert an off-line quadruple at `(γ, t*)` (value `4·Re Fᵢ(1/2+t*+iγ)`),

hit every open half-space: for every `w ≠ 0` some move has negative `w`-component.  This is
the geometric engine of finite evaluation blindness: no nonzero linear functional of the
move values is one-sided.

The proof is a harmonic-function argument.  If all moves were `w`-nonnegative, then
`U_w = Re ∑ wᵢFᵢ` would be nonnegative on the critical line and on both lines
`Re s = 1/2 ± t*` (by the reflection symmetries), hence — by the rectangle maximum principle
and strip decay — on the whole open substrip; the deletion move at `α` forces the interior
zero `U_w(1/2+iα) = 0`; the minimum principle for nonnegative harmonic functions then gives
`U_w ≡ 0` on the substrip, in particular on the critical line, contradicting independence.
-/

namespace RHTower

noncomputable section

open Complex ComplexConjugate InnerProductSpace Metric Set

/-! ## Symmetry collapse of pair and quadruple values -/

/-- Under the reality symmetry a line pair's raw test sum is twice a real part. -/
theorem pair_sum_eq_two_re (F : ℂ → ℂ) (hκ : ∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s))
    (β : ℝ) :
    F (1 / 2 + (β : ℂ) * I) + F (1 / 2 - (β : ℂ) * I)
      = 2 * (((F (1 / 2 + (β : ℂ) * I)).re : ℝ) : ℂ) := by
  have hpt : ((1 : ℂ) / 2 - (β : ℂ) * I) = starRingEnd ℂ (1 / 2 + (β : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [hpt, hκ, Complex.add_conj]
  push_cast
  ring

/-- Under both reflection symmetries an off-line quadruple's raw test sum is four times one
real part. -/
theorem quad_sum_eq_four_re (F : ℂ → ℂ)
    (hκ : ∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s))
    (hσ : ∀ s, F (1 - s) = F s) (t γ : ℝ) :
    F (1 / 2 + (t : ℂ) + (γ : ℂ) * I) + F (1 / 2 - (t : ℂ) + (γ : ℂ) * I)
      + F (1 / 2 + (t : ℂ) - (γ : ℂ) * I) + F (1 / 2 - (t : ℂ) - (γ : ℂ) * I)
      = 4 * (((F (1 / 2 + (t : ℂ) + (γ : ℂ) * I)).re : ℝ) : ℂ) := by
  have hconjpt : ((1 : ℂ) / 2 + (t : ℂ) - (γ : ℂ) * I)
      = starRingEnd ℂ (1 / 2 + (t : ℂ) + (γ : ℂ) * I) := by
    simp [Complex.ext_iff]
  have h₂ : F (1 / 2 - (t : ℂ) + (γ : ℂ) * I) = F (1 / 2 + (t : ℂ) - (γ : ℂ) * I) := by
    have := hσ (1 / 2 - (t : ℂ) + (γ : ℂ) * I)
    have harg : (1 : ℂ) - (1 / 2 - (t : ℂ) + (γ : ℂ) * I)
        = 1 / 2 + (t : ℂ) - (γ : ℂ) * I := by ring
    rw [harg] at this
    exact this.symm
  have h₄ : F (1 / 2 - (t : ℂ) - (γ : ℂ) * I) = F (1 / 2 + (t : ℂ) + (γ : ℂ) * I) := by
    have := hσ (1 / 2 - (t : ℂ) - (γ : ℂ) * I)
    have harg : (1 : ℂ) - (1 / 2 - (t : ℂ) - (γ : ℂ) * I)
        = 1 / 2 + (t : ℂ) + (γ : ℂ) * I := by ring
    rw [harg] at this
    exact this.symm
  rw [h₂, h₄, hconjpt, hκ]
  rw [show F (1 / 2 + (t : ℂ) + (γ : ℂ) * I) + starRingEnd ℂ (F (1 / 2 + (t : ℂ) + (γ : ℂ) * I))
      + starRingEnd ℂ (F (1 / 2 + (t : ℂ) + (γ : ℂ) * I))
      + F (1 / 2 + (t : ℂ) + (γ : ℂ) * I)
    = 2 * (F (1 / 2 + (t : ℂ) + (γ : ℂ) * I)
        + starRingEnd ℂ (F (1 / 2 + (t : ℂ) + (γ : ℂ) * I))) by ring, Complex.add_conj]
  push_cast
  ring

/-! ## The strip and the substrip rectangles -/

/-- The open strip of half-width `θ` around the critical line. -/
def criticalStrip (θ : ℝ) : Set ℂ := {s : ℂ | |s.re - 1 / 2| < θ}

theorem isOpen_criticalStrip (θ : ℝ) : IsOpen (criticalStrip θ) := by
  have : criticalStrip θ = (fun s : ℂ => |s.re - 1 / 2|) ⁻¹' Set.Iio θ := rfl
  rw [this]
  exact IsOpen.preimage (by fun_prop) isOpen_Iio

theorem convex_criticalStrip (θ : ℝ) : Convex ℝ (criticalStrip θ) := by
  have : criticalStrip θ = Complex.reLm ⁻¹' (Metric.ball (1 / 2 : ℝ) θ) := by
    ext s
    simp [criticalStrip, Metric.mem_ball, Real.dist_eq]
  rw [this]
  exact (convex_ball _ _).linear_preimage Complex.reLm

/-! ## Cone fullness -/

/-- **Cone fullness of the critical-locus moves.**  For a symmetric, strip-decaying,
line-independent family of spectral tests, every nonzero direction `w` sees some
configuration move — a line-pair insertion, the deletion of one support pair at `α`, or an
off-line quadruple insertion at displacement `t*` — with strictly negative `w`-component. -/
theorem criticalLocus_move_cone_fullness
    {k : ℕ} (F : Fin k → ℂ → ℂ) {θ tstar : ℝ} (htpos : 0 < tstar) (hθ : tstar < θ)
    (hhol : ∀ i, DifferentiableOn ℂ (F i) (criticalStrip θ))
    (hκ : ∀ i s, F i (starRingEnd ℂ s) = starRingEnd ℂ (F i s))
    (hσ : ∀ i s, F i (1 - s) = F i s)
    (hdecay : ∀ i, ∀ ε > 0, ∃ T : ℝ, ∀ s : ℂ,
      |s.re - 1 / 2| ≤ tstar → T ≤ |s.im| → ‖F i s‖ ≤ ε)
    (hindep : ∀ v : Fin k → ℝ,
      (∀ τ : ℝ, ∑ i, v i * (F i (1 / 2 + (τ : ℂ) * I)).re = 0) → v = 0)
    (α : ℝ) (w : Fin k → ℝ) (hw : w ≠ 0) :
    (∃ β : ℝ, ∑ i, w i * (2 * (F i (1 / 2 + (β : ℂ) * I)).re) < 0) ∨
    (∑ i, w i * (-2 * (F i (1 / 2 + (α : ℂ) * I)).re) < 0) ∨
    (∃ γ : ℝ, ∑ i, w i * (4 * (F i (1 / 2 + (tstar : ℂ) + (γ : ℂ) * I)).re) < 0) := by
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨h1, h2, h3⟩ := hcontra
  -- the combined test and its harmonic real part
  set Fw : ℂ → ℂ := fun s => ∑ i, (w i : ℂ) * F i s with hFw
  set Uw : ℂ → ℝ := fun s => (Fw s).re with hUw
  have hUeq : ∀ s, Uw s = ∑ i, w i * (F i s).re := by
    intro s
    rw [hUw]
    simp only [hFw, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.re_ofReal_mul]
  -- analyticity of the combined test on the strip
  have hFwan : ∀ z ∈ criticalStrip θ, AnalyticAt ℂ Fw z := by
    intro z hz
    have hterm : ∀ i ∈ Finset.univ, AnalyticAt ℂ (fun s => (w i : ℂ) * F i s) z := by
      intro i _
      exact analyticAt_const.mul
        ((hhol i).analyticAt ((isOpen_criticalStrip θ).mem_nhds hz))
    have h := Finset.analyticAt_sum Finset.univ hterm
    rw [Finset.sum_fn] at h
    exact h
  -- nonnegativity on the line
  have hline : ∀ τ : ℝ, 0 ≤ Uw (1 / 2 + (τ : ℂ) * I) := by
    intro τ
    have := h1 τ
    rw [hUeq]
    have hsum : ∑ i, w i * (2 * (F i (1 / 2 + (τ : ℂ) * I)).re)
        = 2 * ∑ i, w i * (F i (1 / 2 + (τ : ℂ) * I)).re := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum] at this
    linarith
  -- the interior zero from the deletion move
  have hzero : Uw (1 / 2 + (α : ℂ) * I) = 0 := by
    have hminus := h2
    have hsum : ∑ i, w i * (-2 * (F i (1 / 2 + (α : ℂ) * I)).re)
        = -2 * ∑ i, w i * (F i (1 / 2 + (α : ℂ) * I)).re := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum] at hminus
    have hplus := hline α
    rw [hUeq] at hplus ⊢
    linarith
  -- nonnegativity on both displaced lines
  have hplusline : ∀ γ : ℝ, 0 ≤ Uw (1 / 2 + (tstar : ℂ) + (γ : ℂ) * I) := by
    intro γ
    have := h3 γ
    rw [hUeq]
    have hsum : ∑ i, w i * (4 * (F i (1 / 2 + (tstar : ℂ) + (γ : ℂ) * I)).re)
        = 4 * ∑ i, w i * (F i (1 / 2 + (tstar : ℂ) + (γ : ℂ) * I)).re := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum] at this
    linarith
  have hUsym : ∀ s : ℂ, Uw (1 - starRingEnd ℂ s) = Uw s := by
    intro s
    rw [hUeq, hUeq]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [show F i (1 - starRingEnd ℂ s) = F i (starRingEnd ℂ s) from hσ i _, hκ i s]
    exact Complex.conj_re _
  have hminusline : ∀ γ : ℝ, 0 ≤ Uw (1 / 2 - (tstar : ℂ) + (γ : ℂ) * I) := by
    intro γ
    have harg : (1 : ℂ) - starRingEnd ℂ (1 / 2 + (tstar : ℂ) + (γ : ℂ) * I)
        = 1 / 2 - (tstar : ℂ) + (γ : ℂ) * I := by
      simp [Complex.ext_iff]
      ring
    have := hUsym (1 / 2 + (tstar : ℂ) + (γ : ℂ) * I)
    rw [harg] at this
    rw [this]
    exact hplusline γ
  -- harmonicity of ±Uw wherever the tests are analytic
  have hUharmAt : ∀ z ∈ criticalStrip θ, HarmonicAt Uw z := by
    intro z hz
    have := (hFwan z hz).harmonicAt_re
    simpa [hUw] using this
  have hUnegharmAt : ∀ z ∈ criticalStrip θ, HarmonicAt (fun s => -Uw s) z := by
    intro z hz
    have hneg : AnalyticAt ℂ (fun s => -Fw s) z := (hFwan z hz).neg
    have := hneg.harmonicAt_re
    have heq : (fun s => ((-Fw s).re)) = fun s => -Uw s := by
      funext s
      simp [hUw]
    rwa [heq] at this
  -- the open substrip
  set Ω : Set ℂ := criticalStrip tstar with hΩ
  have hΩsub : Ω ⊆ criticalStrip θ := fun s hs => lt_trans hs hθ
  -- nonnegativity throughout the substrip by the rectangle maximum principle
  have hUpos : ∀ z ∈ Ω, 0 ≤ Uw z := by
    intro z hz
    by_contra hneg
    push_neg at hneg
    set ε : ℝ := -Uw z / 2 with hε
    have hεpos : 0 < ε := by simp only [hε]; linarith
    -- strip decay of the combined test
    have hWsum : (0 : ℝ) < ∑ i, |w i| + 1 := by positivity
    have hdecayFw : ∃ T : ℝ, ∀ s : ℂ, |s.re - 1 / 2| ≤ tstar → T ≤ |s.im| → ‖Fw s‖ ≤ ε := by
      set ε' : ℝ := ε / (∑ i, |w i| + 1) with hε'
      have hε'pos : 0 < ε' := by positivity
      have hchoice := fun i => hdecay i ε' hε'pos
      choose T hT using hchoice
      refine ⟨1 + ∑ i, |T i|, fun s hre him => ?_⟩
      have hTle : ∀ i, T i ≤ 1 + ∑ j, |T j| := by
        intro i
        have h1' : T i ≤ |T i| := le_abs_self _
        have h2' : |T i| ≤ ∑ j, |T j| :=
          Finset.single_le_sum (f := fun j => |T j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ i)
        linarith
      have hbound : ∀ i, ‖F i s‖ ≤ ε' := fun i => hT i s hre (le_trans (hTle i) him)
      have hnorm : ‖Fw s‖ ≤ ∑ i, |w i| * ε' := by
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hbound i) (abs_nonneg _)
      have hfin : ∑ i, |w i| * ε' = (∑ i, |w i|) * ε' := by
        rw [Finset.sum_mul]
      rw [hfin] at hnorm
      have : (∑ i, |w i|) * ε' ≤ ε := by
        rw [hε']
        rw [div_eq_inv_mul]
        have hle : (∑ i, |w i|) ≤ ∑ i, |w i| + 1 := by linarith
        calc (∑ i, |w i|) * ((∑ i, |w i| + 1)⁻¹ * ε)
            = ((∑ i, |w i|) / (∑ i, |w i| + 1)) * ε := by ring
          _ ≤ 1 * ε := by
              have hq : (∑ i, |w i|) / (∑ i, |w i| + 1) ≤ 1 := by
                rw [div_le_one hWsum]
                linarith
              exact mul_le_mul_of_nonneg_right hq hεpos.le
          _ = ε := one_mul ε
      linarith
    obtain ⟨T, hT⟩ := hdecayFw
    set T' : ℝ := max (max T (|z.im| + 1)) 1 with hT'
    have hT'pos : 0 < T' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hT'T : T ≤ T' := le_trans (le_max_left _ _) (le_max_left _ _)
    have hT'z : |z.im| < T' :=
      lt_of_lt_of_le (by linarith [abs_nonneg z.im])
        (le_trans (le_max_right T (|z.im| + 1)) (le_max_left _ _))
    -- the rectangle
    set R : Set ℂ := {s : ℂ | |s.re - 1 / 2| < tstar ∧ |s.im| < T'} with hR
    have hRopen : IsOpen R := by
      have : R = ((fun s : ℂ => |s.re - 1 / 2|) ⁻¹' Set.Iio tstar)
          ∩ ((fun s : ℂ => |s.im|) ⁻¹' Set.Iio T') := rfl
      rw [this]
      exact (IsOpen.preimage (by fun_prop) isOpen_Iio).inter
        (IsOpen.preimage (by fun_prop) isOpen_Iio)
    have hRconvex : Convex ℝ R := by
      have : R = (Complex.reLm ⁻¹' (Metric.ball (1 / 2 : ℝ) tstar))
          ∩ (Complex.imLm ⁻¹' (Metric.ball (0 : ℝ) T')) := by
        ext s
        simp [hR, Metric.mem_ball, Real.dist_eq]
      rw [this]
      exact ((convex_ball _ _).linear_preimage Complex.reLm).inter
        ((convex_ball _ _).linear_preimage Complex.imLm)
    have hRbounded : Bornology.IsBounded R := by
      refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1 / 2 + tstar + T')).subset ?_
      intro s hs
      rw [Metric.mem_ball, dist_zero_right]
      have h1' : |s.re| ≤ |s.re - 1 / 2| + 1 / 2 := by
        have h2' := abs_add_le (s.re - 1 / 2) (1 / 2)
        have h3' : |s.re| = |(s.re - 1 / 2) + 1 / 2| := by norm_num
        rw [h3']
        exact le_trans h2' (by norm_num)
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ < (|s.re - 1 / 2| + 1 / 2) + T' := by
            have := hs.2
            linarith [h1']
        _ < (tstar + 1 / 2) + T' := by linarith [hs.1]
        _ = 1 / 2 + tstar + T' := by ring
    have hRsubΩ : R ⊆ Ω := fun s hs => hs.1
    have hRsubStrip : R ⊆ criticalStrip θ := fun s hs => hΩsub (hRsubΩ hs)
    have hclosR : closure R ⊆ {s : ℂ | |s.re - 1 / 2| ≤ tstar ∧ |s.im| ≤ T'} := by
      refine closure_minimal ?_ ?_
      · intro s hs
        exact ⟨hs.1.le, hs.2.le⟩
      · have : {s : ℂ | |s.re - 1 / 2| ≤ tstar ∧ |s.im| ≤ T'}
            = ((fun s : ℂ => |s.re - 1 / 2|) ⁻¹' Set.Iic tstar)
              ∩ ((fun s : ℂ => |s.im|) ⁻¹' Set.Iic T') := rfl
        rw [this]
        exact (IsClosed.preimage (by fun_prop) isClosed_Iic).inter
          (IsClosed.preimage (by fun_prop) isClosed_Iic)
    -- the frontier bound
    have hfrontier : ∀ s ∈ frontier R, -Uw s ≤ ε := by
      intro s hsf
      have hscl : s ∈ closure R := frontier_subset_closure hsf
      have hsnotR : s ∉ R := by
        rw [frontier, hRopen.interior_eq] at hsf
        exact hsf.2
      obtain ⟨hre, him⟩ := hclosR hscl
      have hcases : |s.re - 1 / 2| = tstar ∨ |s.im| = T' := by
        by_contra hno
        push_neg at hno
        exact hsnotR ⟨lt_of_le_of_ne hre hno.1, lt_of_le_of_ne him hno.2⟩
      rcases hcases with hvert | hhoriz
      · -- on the vertical boundary lines the function is nonnegative
        have hsval : 0 ≤ Uw s := by
          rcases (abs_eq htpos.le).mp hvert with hplus | hminus
          · -- s.re = 1/2 + tstar
            have hs_eq : s = 1 / 2 + (tstar : ℂ) + ((s.im : ℝ) : ℂ) * I := by
              apply Complex.ext
              · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                  Complex.ofReal_im, Complex.I_re, Complex.I_im]
                norm_num
                linarith
              · simp
            rw [hs_eq]
            exact hplusline s.im
          · -- s.re = 1/2 − tstar
            have hs_eq : s = 1 / 2 - (tstar : ℂ) + ((s.im : ℝ) : ℂ) * I := by
              apply Complex.ext
              · simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                  Complex.ofReal_im, Complex.I_re, Complex.I_im]
                norm_num
                linarith
              · simp
            rw [hs_eq]
            exact hminusline s.im
        linarith
      · -- on the horizontal edges the decay bound applies
        have hTs : T ≤ |s.im| := by rw [hhoriz]; exact hT'T
        have := hT s hre hTs
        have habs : |Uw s| ≤ ‖Fw s‖ := by
          rw [hUw]
          exact Complex.abs_re_le_norm _
        have := abs_le.mp (le_trans habs this)
        linarith [this.1]
    -- maximum principle on the rectangle
    have hharmneg : HarmonicOnNhd (fun s => -Uw s) R :=
      fun x hx => hUnegharmAt x (hRsubStrip hx)
    have hcont : ContinuousOn (fun s => -Uw s) (closure R) := by
      intro s hs
      have hsstrip : s ∈ criticalStrip θ := by
        obtain ⟨hre, _⟩ := hclosR hs
        exact lt_of_le_of_lt hre hθ
      exact ((hUharmAt s hsstrip).1.continuousAt.neg).continuousWithinAt
    have hzR : z ∈ R := ⟨hz, hT'z⟩
    have := Bottcher.harmonic_le_of_frontier_le_of_isPreconnected hRopen hRbounded
      hRconvex.isPreconnected hharmneg hcont hfrontier z hzR
    -- −Uw z = 2ε > ε: contradiction
    rw [hε] at this
    linarith
  -- the minimum principle on the substrip
  have hΩopen : IsOpen Ω := isOpen_criticalStrip tstar
  have hΩconn : IsPreconnected Ω := (convex_criticalStrip tstar).isPreconnected
  have hΩharm : HarmonicOnNhd Uw Ω := fun x hx => hUharmAt x (hΩsub hx)
  have hαΩ : (1 / 2 + (α : ℂ) * I) ∈ Ω := by
    simp only [hΩ, criticalStrip, Set.mem_setOf_eq]
    simp [htpos]
  have hUzero : EqOn Uw 0 Ω :=
    harmonic_eqOn_zero_of_nonneg hΩopen hΩconn hΩharm hUpos hαΩ hzero
  -- the line lies in the substrip: independence kills w
  have hlinezero : ∀ τ : ℝ, ∑ i, w i * (F i (1 / 2 + (τ : ℂ) * I)).re = 0 := by
    intro τ
    have hmem : (1 / 2 + (τ : ℂ) * I) ∈ Ω := by
      simp only [hΩ, criticalStrip, Set.mem_setOf_eq]
      simp [htpos]
    have := hUzero hmem
    rw [hUeq] at this
    simpa using this
  exact hw (hindep w hlinezero)

end

end RHTower
