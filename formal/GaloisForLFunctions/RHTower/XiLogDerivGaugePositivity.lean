import GaloisForLFunctions.RHTower.XiLogDerivEventualPositivityAbscissa

/-!
# Hadamard positivity right of a moving gauge reads the zero-approach rate

Let `g : ℝ → ℝ` be antitone, with `0 ≤ g < ½`.  Consider Hadamard positivity on the region right of
the moving abscissa `½ + g(|Im s|)` at large heights,

`HadamardGaugePositivity g T`: `Re (ξ'/ξ)(s) ≥ 0` whenever `Re s > ½ + g(|Im s|)` and
`|Im s| ≥ T`.

* **Necessity** (`abs_re_sub_half_le_of_hadamardGaugePositivity`).  If it holds, every zero with
  `|γ| ≥ T` has `|β − ½| ≤ g(|γ|)`: just left of a zero right of the line the logarithmic
  derivative tends to `−∞` (`exists_re_logDeriv_xi_neg_near_zero`), and deep zeros on the left are
  reflected to the right.
* **Sufficiency** (`hadamardGaugePositivity_of_abs_re_sub_half_le`).  If every zero with
  `|γ| ≥ T₀` has `|β − ½| ≤ g(|γ| + 1)`, it holds with `T = T₀ + 1`: a zero obstructs at `s` only
  inside the disc `(β − ½)² ≥ (Re s − ½)² + (Im s − γ)²` (`re_logDeriv_xi_nonneg_of_disk_bound`),
  which forces `|Im s − γ| < ½` and then `Re s − ½ > g(|Im s|) ≥ g(|γ| + 1) ≥ |β − ½|`.

So, up to a unit shift of the gauge, Hadamard positivity right of `½ + g` at large heights is
exactly the statement that the zeros approach the line at rate `g`.  A constant gauge recovers the
abscissa law (`eventualHadamardPositivityRight_iff`).  The gauge `g(t) = c/log t` is the critical
scale of shallow off-line pairs: positivity right of `½ + c/log|Im s|` at large heights says that
eventually every zero lies within about `c/log γ` of the line.
-/

open Complex Set

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse

noncomputable section

/-- Hadamard positivity right of the moving abscissa `½ + g(|Im s|)` above height `T`. -/
def HadamardGaugePositivity (g : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ s : ℂ, 1 / 2 + g |s.im| < s.re → T ≤ |s.im| → 0 ≤ (logDeriv xi s).re

/-- **Necessity: positivity right of the gauge bounds the distance of every large zero.** -/
theorem abs_re_sub_half_le_of_hadamardGaugePositivity {g : ℝ → ℝ} {T : ℝ}
    (hP : HadamardGaugePositivity g T) (q : XiZeroCopy) (hq : T ≤ |((q.1 : ℂ)).im|) :
    |((q.1 : ℂ)).re - 1 / 2| ≤ g |((q.1 : ℂ)).im| := by
  -- reduce to a zero right of the line, with the same absolute ordinate
  obtain ⟨q', hre', him'⟩ : ∃ q' : XiZeroCopy, ((q'.1 : ℂ)).re - 1 / 2 =
      |((q.1 : ℂ)).re - 1 / 2| ∧ |((q'.1 : ℂ)).im| = |((q.1 : ℂ)).im| := by
    rcases le_or_gt (1 / 2) ((q.1 : ℂ)).re with h | h
    · exact ⟨q, by rw [abs_of_nonneg (by linarith)], rfl⟩
    · refine ⟨xiZeroCopyReflectEquiv.symm q, ?_, ?_⟩
      · have hr := spectral_im_eq (xiZeroCopyReflectEquiv.symm q)
        rw [xiSpectralPoint_reflect_symm, Complex.neg_im, spectral_im_eq] at hr
        rw [abs_of_neg (by linarith)]
        linarith
      · have hi := spectral_re_eq (xiZeroCopyReflectEquiv.symm q)
        rw [xiSpectralPoint_reflect_symm, Complex.neg_re, spectral_re_eq] at hi
        rw [← hi, abs_neg]
  rw [← hre', ← him']
  by_contra hlt
  push Not at hlt
  set δ : ℝ := ((q'.1 : ℂ)).re - 1 / 2 - g |((q'.1 : ℂ)).im| with hδ
  obtain ⟨ε, hε0, hεδ, hneg⟩ := exists_re_logDeriv_xi_neg_near_zero
    (xi_xiZeroCopy_eq_zero q') (δ := δ) (by rw [hδ]; linarith)
  have hsim : ((q'.1 : ℂ) - ε).im = ((q'.1 : ℂ)).im := by
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hsre : ((q'.1 : ℂ) - ε).re = ((q'.1 : ℂ)).re - ε := by
    simp only [Complex.sub_re, Complex.ofReal_re]
  have h1 : 1 / 2 + g |((q'.1 : ℂ) - ε).im| < ((q'.1 : ℂ) - ε).re := by
    rw [hsim, hsre]; linarith
  have h2 : T ≤ |((q'.1 : ℂ) - ε).im| := by rw [hsim, him']; exact hq
  linarith [hP _ h1 h2]

/-- **Sufficiency: zeros within the shifted gauge give positivity right of the gauge.** -/
theorem hadamardGaugePositivity_of_abs_re_sub_half_le {g : ℝ → ℝ} (hg : Antitone g)
    (hg0 : ∀ t, 0 ≤ g t) {T₀ : ℝ}
    (hz : ∀ q : XiZeroCopy, T₀ ≤ |((q.1 : ℂ)).im| →
      |((q.1 : ℂ)).re - 1 / 2| ≤ g (|((q.1 : ℂ)).im| + 1)) :
    HadamardGaugePositivity g (T₀ + 1) := by
  intro s hs hT
  have hs1 : 1 / 2 < s.re := by linarith [hg0 |s.im|]
  by_cases hxi : xi s = 0
  · rw [logDeriv_xi_eq_zero_of_xi_eq_zero hxi, Complex.zero_re]
  refine re_logDeriv_xi_nonneg_of_disk_bound hs1 hxi fun q => ?_
  have hspec := abs_spectral_im_lt_half q
  rw [spectral_im_eq] at hspec
  have hhalf : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < 1 / 4 := by
    have : |((q.1 : ℂ)).re - 1 / 2| < 1 / 2 := by rw [abs_sub_comm]; exact hspec
    nlinarith [abs_nonneg (((q.1 : ℂ)).re - 1 / 2), sq_abs (((q.1 : ℂ)).re - 1 / 2)]
  by_contra hge
  push Not at hge
  -- an obstructing zero is within height `½` of `s`
  have hclose : (s.im - ((q.1 : ℂ)).im) ^ 2 < 1 / 4 := by
    nlinarith [sq_nonneg (s.re - 1 / 2)]
  have hclose' : |s.im - ((q.1 : ℂ)).im| < 1 / 2 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((s.im - ((q.1 : ℂ)).im) ^ 2) < Real.sqrt (1 / 4) :=
          Real.sqrt_lt_sqrt (sq_nonneg _) hclose
      _ = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have habs := abs_sub_abs_le_abs_sub s.im ((q.1 : ℂ)).im
  have habs' := abs_sub_abs_le_abs_sub ((q.1 : ℂ)).im s.im
  rw [abs_sub_comm] at habs'
  have hqT : T₀ ≤ |((q.1 : ℂ)).im| := by linarith
  have hd := hz q hqT
  have hgmono : g (|((q.1 : ℂ)).im| + 1) ≤ g |s.im| := hg (by linarith)
  have hδ : |((q.1 : ℂ)).re - 1 / 2| < s.re - 1 / 2 := by linarith
  have hsq : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 := by
    have := sq_abs (((q.1 : ℂ)).re - 1 / 2)
    nlinarith [abs_nonneg (((q.1 : ℂ)).re - 1 / 2)]
  nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]

end

end RHTower.BacklundConverse
