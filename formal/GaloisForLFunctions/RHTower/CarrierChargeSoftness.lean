/-
# Symmetry alone does not force the charge: the softness counterexample

The deck charge of an FE- and Schwarz-symmetric carrier is `V₄`-invariant
(`carrierCharge_quadruple`).  Does that symmetry *force* the charge to be trivial off the
critical line?  It does not.  This file exhibits an explicit entire carrier that has both
symmetries and yet carries an odd (nontrivial) charge at an off-line point:

  `f(s) = (s − ρ₀)(s − (1−ρ₀))(s − ρ̄₀)(s − (1−ρ̄₀))`,

the quartic on the full `V₄` orbit of an off-line `ρ₀`.  For `ρ₀` off the critical line and
off the real axis the four orbit points are distinct, so `ρ₀` is a *simple* zero and
`carrierCharge f 1 ρ₀ = (−1)¹ = −1`.

The consequence is sharp: the functional equation and Schwarz reflection are a genuine
constraint on the charge — they pin it to a `V₄`-invariant — but they are **not** the
constraint that trivializes it off the seam.  A second, non-symmetry input is required.
This is the softness end of the Goldilocks trichotomy, made explicit on the charge itself:
the class of FE-symmetric carriers is too soft to force `carrierCharge = 1` off the line.

The witness is an explicit polynomial exhibited to refute a would-be implication; no carrier
is grown by any flow.
-/
import GaloisForLFunctions.RHTower.CarrierDeckCharge

namespace RHTower

open Complex

/-- The `V₄`-orbit quartic of a point `ρ₀`: an entire carrier with zeros exactly at
`{ρ₀, 1−ρ₀, ρ̄₀, 1−ρ̄₀}`. -/
noncomputable def orbitQuartic (ρ₀ : ℂ) : ℂ → ℂ :=
  fun s => (s - ρ₀) * ((s - (1 - ρ₀)) * (s - (starRingEnd ℂ) ρ₀) *
    (s - (1 - (starRingEnd ℂ) ρ₀)))

theorem orbitQuartic_differentiable (ρ₀ : ℂ) : Differentiable ℂ (orbitQuartic ρ₀) := by
  unfold orbitQuartic; fun_prop

/-- The quartic satisfies the functional equation `f(1−s) = f(s)`: its zero set is
`1 − ·`-invariant. -/
theorem orbitQuartic_fe (ρ₀ : ℂ) (s : ℂ) :
    orbitQuartic ρ₀ (1 - s) = orbitQuartic ρ₀ s := by
  unfold orbitQuartic; ring

/-- The quartic is Schwarz-equivariant `f(s̄) = \overline{f(s)}`: its zero set is
conjugation-invariant. -/
theorem orbitQuartic_conj (ρ₀ : ℂ) (s : ℂ) :
    orbitQuartic ρ₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (orbitQuartic ρ₀ s) := by
  unfold orbitQuartic
  simp only [map_mul, map_sub, map_one, Complex.conj_conj]
  ring

/-- At an off-line, off-real point the three non-`ρ₀` orbit factors are nonzero at `ρ₀`. -/
theorem orbitQuartic_cofactor_ne_zero {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) :
    (ρ₀ - (1 - ρ₀)) * (ρ₀ - (starRingEnd ℂ) ρ₀) * (ρ₀ - (1 - (starRingEnd ℂ) ρ₀)) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · -- ρ₀ − (1 − ρ₀) = 2ρ₀ − 1, real part 2ρ₀.re − 1 ≠ 0
    intro h
    apply hre
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  · -- ρ₀ − ρ̄₀ = 2i·Im ρ₀, imaginary part 2 Im ρ₀ ≠ 0
    intro h
    apply him
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
    linarith
  · -- ρ₀ − (1 − ρ̄₀) = 2 Re ρ₀ − 1 (real), real part ≠ 0
    intro h
    apply hre
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at hr
    linarith

/-- At an off-line, off-real point `ρ₀` the quartic has a **simple** zero. -/
theorem orbitQuartic_order_one {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) :
    analyticOrderAt (orbitQuartic ρ₀) ρ₀ = 1 := by
  set g : ℂ → ℂ := fun s => (s - (1 - ρ₀)) * (s - (starRingEnd ℂ) ρ₀) *
    (s - (1 - (starRingEnd ℂ) ρ₀)) with hg
  have hfeq : orbitQuartic ρ₀ = (fun s => s - ρ₀) * g := by
    funext s; simp only [orbitQuartic, hg, Pi.mul_apply]
  have hlin_an : AnalyticAt ℂ (fun s : ℂ => s - ρ₀) ρ₀ := analyticAt_id.sub analyticAt_const
  have hg_an : AnalyticAt ℂ g ρ₀ := by rw [hg]; fun_prop
  have hg0 : g ρ₀ ≠ 0 := orbitQuartic_cofactor_ne_zero hre him
  have hord_lin : analyticOrderAt (fun s : ℂ => s - ρ₀) ρ₀ = 1 := by
    refine hlin_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
    · simp
    · have : deriv (fun s : ℂ => s - ρ₀) ρ₀ = 1 :=
        ((hasDerivAt_id ρ₀).sub_const ρ₀).deriv
      rw [this]; exact one_ne_zero
  have hord_g : analyticOrderAt g ρ₀ = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hg0)
  rw [hfeq, analyticOrderAt_mul hlin_an hg_an, hord_lin, hord_g, add_zero]

/-- **Softness: symmetry does not force the charge.**  For every `ρ₀` off the critical line
and off the real axis there is an entire carrier `f` with the functional equation and Schwarz
reflection whose level-`2` deck charge at `ρ₀` is `−1` — the charge is nontrivial off the
seam.  Hence FE-symmetry alone cannot force `carrierCharge f 1 = 1` off the line: a second,
non-symmetry input is needed. -/
theorem exists_feSchwarz_carrier_odd_charge {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ s, f (1 - s) = f s) ∧
      (∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)) ∧
      carrierCharge f 1 ρ₀ = -1 := by
  refine ⟨orbitQuartic ρ₀, orbitQuartic_differentiable ρ₀, orbitQuartic_fe ρ₀,
    orbitQuartic_conj ρ₀, ?_⟩
  rw [carrierCharge_one_eq_neg_one_pow, orbitQuartic_order_one hre him]
  simp

end RHTower
