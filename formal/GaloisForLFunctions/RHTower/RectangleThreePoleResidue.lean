import GaloisForLFunctions.RHTower.RectangleTwoPoleResidue

/-!
# A three-pole rectangle residue theorem

If a function agrees off three points with three scalar Cauchy kernels plus an entire remainder,
its positively oriented rectangle integral is `2πi` times the sum of the three scalar residues
whenever all three poles lie strictly inside.  The proof splits off one kernel and applies the
two-pole theorem to the rest.
-/

noncomputable section

namespace RHTower

open Complex intervalIntegral Set

/-- A point of a horizontal edge differs from a pole whose imaginary part is strictly off the edge. -/
private theorem horizontal_ne {p : ℂ} {x c : ℝ} (h : c ≠ p.im) : ((x : ℂ) + c * I) ≠ p := by
  intro heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_add, mul_one] at him
  exact h (by simpa using him)

/-- A point of a vertical edge differs from a pole whose real part is strictly off the edge. -/
private theorem vertical_ne {p : ℂ} {c y : ℝ} (h : c ≠ p.re) : ((c : ℂ) + y * I) ≠ p := by
  intro heq
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero] at hre
  exact h (by simpa using hre)

private theorem kernel_intervalIntegrable {a b : ℝ} (pt : ℝ → ℂ) (hpt : Continuous pt)
    (c pole : ℂ) (hne : ∀ t ∈ uIcc a b, pt t ≠ pole) :
    IntervalIntegrable (fun t => c * (pt t - pole)⁻¹) MeasureTheory.volume a b :=
  (continuousOn_const.mul ((hpt.continuousOn.sub continuousOn_const).inv₀
    (fun t ht => sub_ne_zero.mpr (hne t ht)))).intervalIntegrable

theorem rectIntegral_eq_three_pole_residues
    {F R : ℂ → ℂ} {p q r rp rq rr z₁ z₂ : ℂ}
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im)
    (hq1 : z₁.re < q.re) (hq2 : q.re < z₂.re)
    (hq3 : z₁.im < q.im) (hq4 : q.im < z₂.im)
    (hr1 : z₁.re < r.re) (hr2 : r.re < z₂.re)
    (hr3 : z₁.im < r.im) (hr4 : r.im < z₂.im)
    (hR : Differentiable ℂ R)
    (hdecomp : ∀ z, z ≠ p → z ≠ q → z ≠ r →
      F z = rp * (z - p)⁻¹ + (rq * (z - q)⁻¹ + (rr * (z - r)⁻¹ + R z))) :
    rectIntegral F z₁ z₂ = 2 * Real.pi * I * (rp + rq + rr) := by
  let G : ℂ → ℂ := fun z => rp * (z - p)⁻¹ + (rq * (z - q)⁻¹ + R z)
  let H : ℂ → ℂ := fun z => rr * (z - r)⁻¹
  let S : Set ℂ := {z | z ≠ p ∧ z ≠ q ∧ z ≠ r}
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S := fun x _ =>
    ⟨horizontal_ne hp3.ne, horizontal_ne hq3.ne, horizontal_ne hr3.ne⟩
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S := fun x _ =>
    ⟨horizontal_ne hp4.ne', horizontal_ne hq4.ne', horizontal_ne hr4.ne'⟩
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S := fun y _ =>
    ⟨vertical_ne hp2.ne', vertical_ne hq2.ne', vertical_ne hr2.ne'⟩
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S := fun y _ =>
    ⟨vertical_ne hp1.ne, vertical_ne hq1.ne, vertical_ne hr1.ne⟩
  have hGH : ∀ z ∈ S, F z = G z + H z := by
    intro z hz
    rw [hdecomp z hz.1 hz.2.1 hz.2.2]
    simp only [G, H]
    ring
  have hregular : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      IntervalIntegrable (fun t => R (pt t)) MeasureTheory.volume a b :=
    fun pt hpt => (hR.continuous.comp hpt).intervalIntegrable _ _
  have hGint : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ t ∈ uIcc a b, pt t ∈ S) →
      IntervalIntegrable (fun t => G (pt t)) MeasureTheory.volume a b := by
    intro a b pt hpt hS
    exact (kernel_intervalIntegrable pt hpt rp p (fun t ht => (hS t ht).1)).add
      ((kernel_intervalIntegrable pt hpt rq q (fun t ht => (hS t ht).2.1)).add
        (hregular pt hpt))
  have hHint : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ t ∈ uIcc a b, pt t ∈ S) →
      IntervalIntegrable (fun t => H (pt t)) MeasureTheory.volume a b :=
    fun pt hpt hS => kernel_intervalIntegrable pt hpt rr r (fun t ht => (hS t ht).2.2)
  rw [rectIntegral_congr hGH hbot htop hright hleft,
    rectIntegral_add (hGint _ (by fun_prop) hbot) (hHint _ (by fun_prop) hbot)
      (hGint _ (by fun_prop) htop) (hHint _ (by fun_prop) htop)
      (hGint _ (by fun_prop) hright) (hHint _ (by fun_prop) hright)
      (hGint _ (by fun_prop) hleft) (hHint _ (by fun_prop) hleft),
    rectIntegral_eq_two_pole_residues hp1 hp2 hp3 hp4 hq1 hq2 hq3 hq4 hR
      (fun z _ _ => rfl)]
  show _ + rectIntegral (fun z => rr * (z - r)⁻¹) z₁ z₂ = _
  rw [rectIntegral_const_mul, rectIntegral_cauchyKernel hr1 hr2 hr3 hr4]
  ring

end RHTower
