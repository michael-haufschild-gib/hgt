import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.CriticalDiscsAndTheTerminalLens
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheDyadicAmplificationOfTheHeckeDefect
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.RightQuadraticTerminalsNearOffLineZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalOutwardLogDeriv
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip

/-!
# The terminal ceiling and the one-scale bound are zero-free strips

Two source-side targets of the field are measured exactly by the width of a zero-free strip.

* **Terminal ceiling** (`exists_terminal_of_depth_lt`, `zeroFreeStrip_iff_terminal_ceiling`). Every
  zero of depth `> a` ascends (ACP) to a right terminal of depth `> a`. So a ceiling excluding
  terminals of depth `> a` is equivalent to the zero-free strip `|Re ρ − ½| ≤ a`; at `a = 0`, RH is
  the absence of right terminals (`riemannHypothesis_iff_no_right_terminal`).
* **One-scale bound** (`zeroFreeStrip_iff_heckeDefect_bound`). The bound
  `E_f(L) ≤ D(f)(2cosh(2ϑL) − 2)` for every compact `C²` test and every scale is equivalent to the
  zero-free strip of width `ϑ`. A zero of depth `d > ϑ` seen by `f` forces
  `E_f(L) ≥ w(2cosh(2dL) − 2)`, which outgrows `D(2cosh(2ϑL) − 2)`
  (`not_forall_kernel_le`).

So no input weaker than a zero-free strip reaches either target, and a strip reaches both: these
are the graded forms of RH in the language of terminals and of Hecke defects.
-/

noncomputable section

open Filter Topology RHTower

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ArithmeticCorrespondencePositivity Zeta23 GaloisForLFunctions.ConjugateDiagonalGeometry
  GaloisForLFunctions.ArithmeticPolarization

/-! ### The terminal ceiling -/

/-- **Ascent to terminals.** A zero of depth `> a` yields a right terminal of depth `> a`. -/
theorem exists_terminal_of_depth_lt {a : ℝ} (ha : 0 ≤ a) {q : XiZeroCopy}
    (hq : a < xiZeroDepth q) :
    ∃ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re ∧ IsTerminal p ∧ a < xiZeroDepth p := by
  obtain ⟨C, -, hterm⟩ := exists_right_xi_quadratic_terminal_near
  -- Move to the right of the critical line by the line reflection.
  have hright : ∃ q' : XiZeroCopy, 1 / 2 < (q'.1 : ℂ).re ∧ xiZeroDepth q' = xiZeroDepth q := by
    by_cases hqr : 1 / 2 < (q.1 : ℂ).re
    · exact ⟨q, hqr, rfl⟩
    · refine ⟨xiZeroCopyLineConjEquiv q, ?_, ?_⟩
      · rw [(xiLineConj_coordinates q).1]
        have : (q.1 : ℂ).re - 1 / 2 ≠ 0 := by
          intro h0
          have : xiZeroDepth q = 0 := by rw [xiZeroDepth, h0, abs_zero]
          linarith
        have : (q.1 : ℂ).re < 1 / 2 := lt_of_le_of_ne (not_lt.mp hqr) (by
          intro h; apply this; linarith)
        linarith
      · simp only [xiZeroDepth]
        rw [(xiLineConj_coordinates q).1, show 1 - (q.1 : ℂ).re - 1 / 2 =
          -((q.1 : ℂ).re - 1 / 2) by ring, abs_neg]
  obtain ⟨q', hq'r, hq'd⟩ := hright
  obtain ⟨p, hpr, -, hpd, hpc⟩ := hterm q' hq'r
  exact ⟨p, hpr, hpc, lt_of_lt_of_le (hq'd ▸ hq) hpd⟩

/-- **The terminal ceiling is the zero-free strip.** For `a ≥ 0`, all zeros have depth `≤ a` iff all
right terminals do. -/
theorem zeroFreeStrip_iff_terminal_ceiling {a : ℝ} (ha : 0 ≤ a) :
    (∀ q : XiZeroCopy, xiZeroDepth q ≤ a) ↔
      ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re → IsTerminal p → xiZeroDepth p ≤ a := by
  constructor
  · exact fun h p _ _ => h p
  · intro h q
    by_contra hlt
    obtain ⟨p, hpr, hpt, hpd⟩ := exists_terminal_of_depth_lt ha (not_le.mp hlt)
    exact absurd (h p hpr hpt) (not_le.mpr hpd)

/-- **RH is the absence of right terminals.** -/
theorem riemannHypothesis_iff_no_right_terminal :
    RiemannHypothesis ↔ ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re → ¬ IsTerminal p := by
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero]
  have hdepth : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 ↔ xiZeroDepth q ≤ 0 := by
    intro q
    have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
      simp [xiSpectralPoint, Complex.mul_im]
    rw [him, xiZeroDepth, abs_nonpos_iff, neg_eq_zero]
  simp_rw [hdepth]
  rw [zeroFreeStrip_iff_terminal_ceiling le_rfl]
  constructor
  · intro h p hpr hpt
    have := h p hpr hpt
    have : 0 < xiZeroDepth p := by
      rw [xiZeroDepth, abs_of_pos (by linarith)]; linarith
    linarith
  · intro h p hpr hpt
    exact absurd hpt (h p hpr)

/-! ### The one-scale bound -/

/-- A defect bound with angle `ϑ` cannot dominate a single seen zero of depth `d > ϑ` at every
scale: at `L = log M/(2(d − ϑ))` with `M = (2D + 2w)/w + 1` the zero outgrows the bound. -/
theorem not_forall_kernel_le {w D ϑ d : ℝ} (hw : 0 < w) (hD : 0 ≤ D) (hϑ : 0 ≤ ϑ) (hd : ϑ < d) :
    ¬ ∀ L : ℝ, 0 ≤ L →
      w * (2 * Real.cosh (2 * d * L) - 2) ≤ D * (2 * Real.cosh (2 * ϑ * L) - 2) := by
  intro h
  set M : ℝ := (2 * D + 2 * w) / w + 1
  have hM0 : 0 < (2 * D + 2 * w) / w := by positivity
  have hM : 1 < M := by show 1 < (2 * D + 2 * w) / w + 1; linarith
  set L : ℝ := Real.log M / (2 * (d - ϑ))
  have hne' : d - ϑ ≠ 0 := (sub_pos.mpr hd).ne'
  have hne : 2 * (d - ϑ) ≠ 0 := mul_ne_zero two_ne_zero hne'
  have hL : 0 ≤ L := div_nonneg (Real.log_nonneg hM.le) (by linarith)
  have hu : Real.exp (2 * (d - ϑ) * L) = M := by
    rw [show 2 * (d - ϑ) * L = Real.log M by simp only [L]; field_simp, Real.exp_log (by linarith)]
  set v : ℝ := Real.exp (2 * ϑ * L)
  have hv : 1 ≤ v := Real.one_le_exp (by positivity)
  have hdL : Real.exp (2 * d * L) = M * v := by
    rw [← hu, ← Real.exp_add]; congr 1; ring
  have hlow : Real.exp (2 * d * L) ≤ 2 * Real.cosh (2 * d * L) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(2 * d * L))]
  have hup : 2 * Real.cosh (2 * ϑ * L) - 2 ≤ 2 * v := by
    rw [Real.cosh_eq]
    have : Real.exp (-(2 * ϑ * L)) ≤ v := by
      simp only [v]; exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have h1 := h L hL
  have h2 : w * (M * v - 2) ≤ D * (2 * v) := by
    calc w * (M * v - 2) ≤ w * (2 * Real.cosh (2 * d * L) - 2) := by
          apply mul_le_mul_of_nonneg_left _ hw.le; rw [← hdL]; linarith
      _ ≤ D * (2 * Real.cosh (2 * ϑ * L) - 2) := h1
      _ ≤ D * (2 * v) := mul_le_mul_of_nonneg_left hup hD
  have h3 : w * M ≤ 2 * D + 2 * w := by
    have hv0 : 0 < v := by linarith
    have : w * M * v ≤ (2 * D + 2 * w) * v := by nlinarith
    exact le_of_mul_le_mul_right this hv0
  have h4 : M ≤ (2 * D + 2 * w) / w := by rw [le_div_iff₀ hw]; linarith
  linarith

/-- **The one-scale bound is the zero-free strip.** For `ϑ ≥ 0`, every zero has depth `≤ ϑ` iff
`E_f(L) ≤ D(f)(2cosh(2ϑL) − 2)` for every compact `C²` test and every scale `L`. -/
theorem zeroFreeStrip_iff_heckeDefect_bound {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    (∀ ρ : zetaZeroConfig.carrier, |zetaDepth ρ| ≤ ϑ) ↔
      ∀ (f : CompactTest) (L : ℝ), heckeDefect f L ≤ mass f * (2 * Real.cosh (2 * ϑ * L) - 2) := by
  constructor
  · intro h f L
    have hk : ∀ ρ, depthKernel L (zetaDepth ρ) ≤ depthKernel L ϑ := fun ρ =>
      depthKernel_mono_depth L (by rw [abs_of_nonneg hϑ]; exact h ρ)
    rw [heckeDefect, mass, collidedForm, ← tsum_mul_right]
    refine (summable_heckeDefect f L).tsum_le_tsum (fun ρ => ?_)
      ((summable_zetaWeight f).mul_right _)
    change zetaWeight f ρ * depthKernel L (zetaDepth ρ) ≤
      zetaWeight f ρ * (2 * Real.cosh (2 * ϑ * L) - 2)
    have : depthKernel L ϑ = 2 * Real.cosh (2 * ϑ * L) - 2 := rfl
    rw [← this]
    exact mul_le_mul_of_nonneg_left (hk ρ) (zetaWeight_nonneg f ρ)
  · intro h ρ₀
    by_contra hlt
    rw [not_le] at hlt
    set s : ℂ := (ρ₀ : ℂ)
    have hmem : s ∈ zetaZeroConfig.carrier := ρ₀.2
    obtain ⟨⟨⟨g, hgreal⟩, _hgsupp⟩, hg0, -⟩ :=
      ArithmeticCorrespondencePositivity.exists_mem_realTestsAt_mellinAt_ne_zero one_pos s s
    set f : CompactTest := ⟨fun u => (g u : ℂ),
      Complex.ofRealCLM.contDiff.comp hgreal.1, hgreal.2.comp_left Complex.ofReal_zero⟩
    have htr : tr f.1 s ≠ 0 := by rw [tr_cx_eq_mellinAt]; exact hg0
    have hw : 0 < zetaWeight f ρ₀ := by
      have hm : (1 : ℝ) ≤ zetaZeroConfig.mult ρ₀ := by
        exact_mod_cast zetaZeroConfig.one_le_mult s hmem
      exact mul_pos (by linarith) (Complex.normSq_pos.mpr htr)
    apply not_forall_kernel_le hw (mass_nonneg f) hϑ hlt
    intro L _
    have hsingle : zetaWeight f ρ₀ * depthKernel L (zetaDepth ρ₀) ≤ heckeDefect f L :=
      (summable_heckeDefect f L).le_tsum ρ₀ fun ρ _ =>
        mul_nonneg (zetaWeight_nonneg f ρ) (depthKernel_nonneg _ _)
    have hk : depthKernel L (zetaDepth ρ₀) = 2 * Real.cosh (2 * |zetaDepth ρ₀| * L) - 2 := by
      simp only [depthKernel]
      rcases abs_choice (zetaDepth ρ₀) with h' | h' <;> rw [h']
      rw [show 2 * -zetaDepth ρ₀ * L = -(2 * zetaDepth ρ₀ * L) by ring, Real.cosh_neg]
    rw [hk] at hsingle
    exact hsingle.trans (h f L)

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
