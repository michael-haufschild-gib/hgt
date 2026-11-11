import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentExpansionIsAConstituentInAStrip
import GaloisForLFunctions.HTGeometry.AlmostPeriodicDivisorsHaveBoundedLocalMass

/-!
# Uniform local multiplicity of Wiener zeros

After rotation, `F(σ + iz)` is an absolutely convergent exponential series
whose horizontal-strip weights are exactly the Wiener weights of `F`.
Compact translates and Jensen then bound the zero divisor in height windows
uniformly on every smaller closed strip.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

/-- Rotating a Wiener expansion turns its vertical translates into compact
real translates on the corresponding horizontal strip. -/
theorem hasCompactImStripTranslates_rotated_expansion {c : Scale → ℂ} {σ r : ℝ}
    (hr : 0 ≤ r) (hc : WSummable (σ - r) (σ + r) c) :
    HTGeometry.HasCompactImStripTranslates
      (fun z => expansion c ((σ : ℂ) + I * z)) r := by
  have hweight : ∀ q : Scale,
      ‖c q * q.cpow (σ : ℂ)‖ * Real.exp (|q.log| * r) =
        ‖c q‖ * stripWeight (σ - r) (σ + r) q := by
    intro q
    rw [norm_mul, Scale.norm_cpow, Complex.ofReal_re, mul_assoc]
    congr 1
    simp only [stripWeight, Real.rpow_def_of_pos q.toReal_pos, Scale.log]
    rw [← Real.exp_add]
    by_cases hlog : 0 ≤ Real.log q.toReal
    · rw [abs_of_nonneg hlog]
      rw [max_eq_right (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hlog hr]))]
      congr 1
      ring
    · rw [abs_of_neg (lt_of_not_ge hlog)]
      rw [max_eq_left (Real.exp_le_exp.mpr (by
        nlinarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hlog) hr]))]
      congr 1
      ring
  have hs : Summable fun q : Scale =>
      ‖c q * q.cpow (σ : ℂ)‖ * Real.exp (|q.log| * r) +
        ‖(0 : ℂ)‖ * Real.exp (|(0 : ℝ)| * r) := by
    simpa only [hweight, norm_zero, zero_mul, add_zero, WSummable] using hc
  have h := HTGeometry.hasCompactImStripTranslates_tsum
    (fun q => c q * q.cpow (σ : ℂ)) (fun _ : Scale => (0 : ℂ))
    (fun q => q.log) (fun _ : Scale => (0 : ℝ)) hs
  have heq : (fun z : ℂ => ∑' q : Scale,
      ((c q * q.cpow (σ : ℂ)) * cexp (I * q.log * z) + 0 * cexp (I * (0 : ℝ) * z))) =
      fun z => expansion c ((σ : ℂ) + I * z) := by
    funext z
    apply tsum_congr
    intro q
    simp only [zero_mul, add_zero, mul_assoc, Scale.cpow_eq_exp, ← Complex.exp_add]
    congr 2
    ring
  rw [heq] at h
  exact h

private theorem differentiableOn_rotated_expansion {c : Scale → ℂ} {σ ω : ℝ}
    (hc : WSummable (σ - ω) (σ + ω) c) :
    DifferentiableOn ℂ (fun z => expansion c ((σ : ℂ) + I * z)) (HTGeometry.imStrip ω) := by
  intro z hz
  have hz' := abs_lt.mp (HTGeometry.mem_imStrip.mp hz)
  have hmem : σ - ω < ((σ : ℂ) + I * z).re ∧
      ((σ : ℂ) + I * z).re < σ + ω := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_mul_re]
    constructor <;> linarith only [hz'.1, hz'.2]
  have houter : DifferentiableAt ℂ (expansion c) ((σ : ℂ) + I * z) :=
    (differentiableOn_expansion hc).differentiableAt ((isOpen_openStrip _ _).mem_nhds hmem)
  have hinner : DifferentiableAt ℂ (fun w : ℂ => (σ : ℂ) + I * w) z := by fun_prop
  exact (houter.comp z hinner).differentiableWithinAt

private theorem rotated_expansion_order (c : Scale → ℂ) (σ : ℝ) (z : ℂ) :
    analyticOrderNatAt (fun w => expansion c ((σ : ℂ) + I * w)) z =
      analyticOrderNatAt (expansion c) ((σ : ℂ) + I * z) := by
  have hd : deriv (fun w : ℂ => (σ : ℂ) + I * w) z = I := by
    convert! (((hasDerivAt_id z).const_mul I).const_add (σ : ℂ)).deriv using 1 <;> simp
  have ha : AnalyticAt ℂ (fun w : ℂ => (σ : ℂ) + I * w) z := by fun_prop
  unfold analyticOrderNatAt
  exact congrArg ENat.toNat (analyticOrderAt_comp_of_deriv_ne_zero
    (f := expansion c) ha (by rw [hd]; exact I_ne_zero))

/-- In a strictly smaller strip, every height window of a fixed positive length
contains uniformly bounded total multiplicity, including complex off-line zeros. -/
theorem exists_local_expansion_divisor_bound {c : Scale → ℂ} {σ ω a : ℝ}
    (hc : WSummable (σ - ω) (σ + ω) c) (hne : c ≠ 0) (ha : 0 ≤ a) (haω : a < ω) :
    ∃ L > 0, ∃ N ≥ 0, ∀ t : ℝ, ∀ s : Finset ℂ,
      (∀ z ∈ s, |z.re - σ| ≤ a ∧ t ≤ z.im ∧ z.im ≤ t + L) →
      (∑ z ∈ s, (analyticOrderNatAt (expansion c) z : ℝ)) ≤ N := by
  classical
  let r := (a + ω) / 2
  have hr : 0 < r := by dsimp [r]; linarith only [ha, haω]
  have har : a < r := by dsimp [r]; linarith only [haω]
  have hrω : r < ω := by dsimp [r]; linarith only [haω]
  let rot : ℂ → ℂ := fun z => -I * (z - (σ : ℂ))
  have hrot : ∀ z, (σ : ℂ) + I * rot z = z := by
    intro z
    dsimp [rot]
    linear_combination -(z - (σ : ℂ)) * I_mul_I
  have hinj : Function.Injective rot := by
    intro z w h
    calc z = (σ : ℂ) + I * rot z := (hrot z).symm
      _ = (σ : ℂ) + I * rot w := by rw [h]
      _ = w := hrot w
  obtain ⟨z₀, hz₀, hfz₀⟩ : ∃ z : ℂ, z.re = σ ∧ expansion c z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine eq_zero_of_expansion_eq_zero (le_refl σ)
      (hc.mono (by linarith only [ha, haω]) le_rfl (by linarith only [ha, haω])) ?_
    intro z h1 h2
    exact hcon z (le_antisymm h2 h1)
  have hcompact := hasCompactImStripTranslates_rotated_expansion (σ := σ) (r := r) hr.le
    (hc.mono (by linarith only [hrω]) (by linarith only [hr]) (by linarith only [hrω]))
  have hzrot : rot z₀ ∈ HTGeometry.imStrip r := by
    change |(rot z₀).im| < r
    simpa only [rot, neg_mul, Complex.neg_im, Complex.I_mul_im,
      Complex.sub_re, Complex.ofReal_re, hz₀, sub_self, neg_zero, abs_zero] using hr
  obtain ⟨L, hL, N, hN, hbound⟩ := hcompact.exists_local_divisor_bound hr hrω
    (differentiableOn_rotated_expansion hc) hzrot (by rw [hrot]; exact hfz₀) ha har
  refine ⟨L, hL, N, hN, fun t s hs => ?_⟩
  have hb := hbound t (s.image rot) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have hz' := hs z hz
    simpa only [rot, neg_mul, Complex.neg_re, Complex.neg_im,
      Complex.I_mul_re, Complex.I_mul_im, Complex.sub_im, Complex.ofReal_im,
      sub_zero, neg_neg, Complex.sub_re, Complex.ofReal_re, abs_neg]
      using And.intro hz'.2.1 (And.intro hz'.2.2 hz'.1))
  rw [Finset.sum_image (fun z _ w _ h => hinj h)] at hb
  simpa only [rotated_expansion_order, hrot] using hb

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
