import GaloisForLFunctions.RHTower.CriticalLinePoissonPotential

/-!
# The orbit quadratic and its discriminant

The critical-line potential decides the hypothesis but is not holomorphic: its summand carries the
weight `(Re ρ − 1/2)²`, which no Hadamard product or logarithmic derivative produces. This module
locates the obstruction exactly, and it turns out not to be the non-holomorphy itself.

Attach to each zero the monic quadratic cutting out its functional-equation orbit,

  `Q_ρ(s) = (s − ρ)(s − (1 − ρ̄))`.

Three facts:

* its discriminant is the constant `(2 Re ρ − 1)²`, four times the squared displacement;
* on the critical line it is real and non-positive, `Q_ρ(1/2 + it) = −[(Re ρ − 1/2)² + (t − Im ρ)²]`;
* consequently the bump of the potential is the **discriminant ratio**

    `bump_ρ(t) = − disc(Q_ρ) / (4 Q_ρ(1/2 + it))`.

Every ingredient on the right is a holomorphic function of `s` once the orbit is known. So the
summand of the potential is not intrinsically non-holomorphic: what is missing is the *matching*
`ρ ↦ 1 − ρ̄`, that is, a factorisation of the divisor into functional-equation orbits. The analytic
obstruction to the critical-weight reader and the arithmetic obstruction to a canonical half-divisor
are the same obstruction.

This also reformulates the hypothesis as a statement of pure algebra:

  **the hypothesis holds if and only if every orbit quadratic is a perfect square**,

equivalently every orbit discriminant vanishes, equivalently the divisor is a square for the
functional-equation involution. The potential is the generating function of the discriminants.

Finally the threshold improves. At the ordinate of an off-line zero *two* zeros sit — the zero and
its partner, which share that ordinate — and each contributes a full unit, so the potential is at
least `2` there. The hypothesis is the threshold `U < 2`, with a factor of two of room.

## Weight

The same computation explains why the neighbouring lanes closed. A reader that weights a zero by
`δ²/(δ² + τ²)^k` receives `δ^{2−2k}` from that zero at its own ordinate. At `k = 0` the signal
vanishes with the displacement — that is the mass family, and every averaged criterion lives there.
At `k = 2` it diverges — that is the Laguerre expression, whose divergence must be cancelled against
an uncontrolled sum over the remaining zeros, which is what made the inner-band route circular.
Only `k = 1` receives a signal that is a nonzero constant independent of the displacement.
-/

open Complex

namespace RHTower

noncomputable section

/-- The point of the critical line at ordinate `t`. -/
def critAxisPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem critAxisPoint_re (t : ℝ) : (critAxisPoint t).re = 1 / 2 := by
  simp [critAxisPoint]

@[simp] theorem critAxisPoint_im (t : ℝ) : (critAxisPoint t).im = t := by
  simp [critAxisPoint]

/-- The monic quadratic cutting out the functional-equation orbit of a zero. -/
def xiOrbitQuadratic (ρ : XiDivisorSupport) (s : ℂ) : ℂ :=
  (s - (ρ : ℂ)) * (s - ((supportPartner ρ : XiDivisorSupport) : ℂ))

/-- The discriminant of the orbit quadratic: four times the squared displacement. -/
def xiOrbitDiscriminant (ρ : XiDivisorSupport) : ℝ := (2 * (ρ : ℂ).re - 1) ^ (2 : ℕ)

theorem xiOrbitDiscriminant_nonneg (ρ : XiDivisorSupport) : 0 ≤ xiOrbitDiscriminant ρ :=
  sq_nonneg _

/-- The discriminant is the square of the difference of the two roots. -/
theorem xiOrbitDiscriminant_eq_sq (ρ : XiDivisorSupport) :
    ((xiOrbitDiscriminant ρ : ℝ) : ℂ)
      = ((ρ : ℂ) - ((supportPartner ρ : XiDivisorSupport) : ℂ)) ^ (2 : ℕ) := by
  rw [sub_supportPartner_eq, xiOrbitDiscriminant]
  push_cast
  ring

theorem xiOrbitDiscriminant_eq_zero_iff (ρ : XiDivisorSupport) :
    xiOrbitDiscriminant ρ = 0 ↔ (ρ : ℂ).re = 1 / 2 := by
  rw [xiOrbitDiscriminant, sq_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-- **On the critical line the orbit quadratic is real and non-positive.** -/
theorem xiOrbitQuadratic_critAxisPoint (t : ℝ) (ρ : XiDivisorSupport) :
    xiOrbitQuadratic ρ (critAxisPoint t)
      = -(((((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (ρ : ℂ).im) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  have hre : ((supportPartner ρ : XiDivisorSupport) : ℂ).re = 1 - (ρ : ℂ).re :=
    supportPartner_re ρ
  have him : ((supportPartner ρ : XiDivisorSupport) : ℂ).im = (ρ : ℂ).im :=
    supportPartner_im ρ
  refine Complex.ext ?_ ?_ <;>
    simp only [xiOrbitQuadratic, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      critAxisPoint_re, critAxisPoint_im, hre, him, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero] <;>
    ring

/-- **The discriminant ratio.** The bump of the critical-line potential is minus the discriminant of
the orbit quadratic over four times its value. -/
theorem poissonBumpTerm_eq_discriminant_ratio (t : ℝ) (ρ : XiDivisorSupport) :
    poissonBumpTerm t ρ
      = xiOrbitDiscriminant ρ
        / (4 * (((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (ρ : ℂ).im) ^ (2 : ℕ))) := by
  rw [poissonBumpTerm, xiOrbitDiscriminant,
    show (2 * (ρ : ℂ).re - 1) ^ (2 : ℕ) = 4 * ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) by ring,
    mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]

/-- The same identity in the complex form that exhibits the holomorphic dependence on `s`. -/
theorem poissonBumpTerm_eq_neg_discriminant_div (t : ℝ) (ρ : XiDivisorSupport)
    (h : xiOrbitQuadratic ρ (critAxisPoint t) ≠ 0) :
    ((poissonBumpTerm t ρ : ℝ) : ℂ)
      = -(xiOrbitDiscriminant ρ : ℂ) / (4 * xiOrbitQuadratic ρ (critAxisPoint t)) := by
  have hne : ((((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (ρ : ℂ).im) ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro hc
    exact h (by rw [xiOrbitQuadratic_critAxisPoint, hc, neg_zero])
  rw [xiOrbitQuadratic_critAxisPoint, poissonBumpTerm_eq_discriminant_ratio]
  push_cast
  field_simp

/-- **The orbit quadratic is a perfect square exactly on the critical line.** -/
theorem xiOrbitQuadratic_eq_sq_iff (ρ : XiDivisorSupport) :
    (xiOrbitQuadratic ρ = fun s => (s - (ρ : ℂ)) ^ (2 : ℕ)) ↔ (ρ : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have h1 := congrFun h ((ρ : ℂ) + 1)
    rw [xiOrbitQuadratic] at h1
    simp only [add_sub_cancel_left, one_pow, one_mul] at h1
    have h2 : ((supportPartner ρ : XiDivisorSupport) : ℂ) = (ρ : ℂ) := by
      linear_combination -h1
    exact (supportPartner_eq_self_iff ρ).mp (Subtype.ext h2)
  · intro h
    funext s
    rw [xiOrbitQuadratic, (supportPartner_eq_self_iff ρ).mpr h, sq]

/-- **The hypothesis is the vanishing of every orbit discriminant.** -/
theorem riemannHypothesis_iff_forall_xiOrbitDiscriminant_eq_zero :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, xiOrbitDiscriminant ρ = 0 := by
  constructor
  · intro h ρ
    refine (xiOrbitDiscriminant_eq_zero_iff ρ).mpr ?_
    exact (supportPartner_eq_self_iff ρ).mp (riemannHypothesis_iff_supportPartner_eq_id.mp h ρ)
  · intro h
    exact riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ =>
      (xiOrbitDiscriminant_eq_zero_iff ρ).mp (h ρ)

/-- **The hypothesis is the squareness of the divisor under the functional equation.** -/
theorem riemannHypothesis_iff_forall_xiOrbitQuadratic_eq_sq :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport,
      xiOrbitQuadratic ρ = fun s => (s - (ρ : ℂ)) ^ (2 : ℕ) := by
  constructor
  · intro h ρ
    exact (xiOrbitQuadratic_eq_sq_iff ρ).mpr
      ((supportPartner_eq_self_iff ρ).mp (riemannHypothesis_iff_supportPartner_eq_id.mp h ρ))
  · intro h
    exact riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ =>
      (xiOrbitQuadratic_eq_sq_iff ρ).mp (h ρ)

/-- **The threshold is two.** At the ordinate of an off-line zero the zero and its partner both sit,
and each contributes a full unit to the potential. -/
theorem two_le_poissonPotential {ρ : XiDivisorSupport} (h : (ρ : ℂ).re ≠ 1 / 2) :
    2 ≤ poissonPotential ((ρ : ℂ).im) := by
  classical
  have hσ : supportPartner ρ ≠ ρ := fun hc => h ((supportPartner_eq_self_iff ρ).mp hc)
  have hσre : ((supportPartner ρ : XiDivisorSupport) : ℂ).re ≠ 1 / 2 := by
    rw [supportPartner_re]
    intro hc
    exact h (by linarith)
  have hterm₁ : poissonBumpTerm ((ρ : ℂ).im) ρ = 1 := poissonBumpTerm_self h
  have hterm₂ : poissonBumpTerm ((ρ : ℂ).im) (supportPartner ρ) = 1 := by
    have := poissonBumpTerm_self hσre
    rwa [supportPartner_im] at this
  have hsum := Summable.sum_le_tsum (f := fun q => poissonBumpTerm ((ρ : ℂ).im) q)
    {ρ, supportPartner ρ} (fun i _ => poissonBumpTerm_nonneg _ i)
    (summable_poissonBumpTerm ((ρ : ℂ).im))
  rw [Finset.sum_pair (Ne.symm hσ), hterm₁, hterm₂] at hsum
  rw [poissonPotential]
  linarith

/-- The hypothesis in the improved threshold form. -/
theorem riemannHypothesis_iff_forall_poissonPotential_lt_two :
    RiemannHypothesis ↔ ∀ t : ℝ, poissonPotential t < 2 := by
  constructor
  · intro h t
    rw [poissonPotential_eq_zero_of_riemannHypothesis h t]
    norm_num
  · intro h
    refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
    by_contra hc
    exact absurd (two_le_poissonPotential hc) (not_le.mpr (h ((ρ : ℂ).im)))

/-- The signal a weight-`k` reader receives from a zero at its own ordinate. -/
def weightedSelfTerm (k : ℕ) (d : ℝ) : ℝ := d ^ (2 : ℕ) / (d ^ (2 : ℕ)) ^ k

@[simp] theorem weightedSelfTerm_zero (d : ℝ) : weightedSelfTerm 0 d = d ^ (2 : ℕ) := by
  simp [weightedSelfTerm]

/-- **The critical weight.** At `k = 1` the signal is one, independent of the displacement. -/
theorem weightedSelfTerm_one {d : ℝ} (hd : d ≠ 0) : weightedSelfTerm 1 d = 1 := by
  rw [weightedSelfTerm, pow_one, div_self (pow_ne_zero _ hd)]

/-- At `k = 2`, the Laguerre weight, the signal diverges as the zero approaches the line. -/
theorem weightedSelfTerm_two {d : ℝ} (hd : d ≠ 0) : weightedSelfTerm 2 d = 1 / d ^ (2 : ℕ) := by
  rw [weightedSelfTerm]
  field_simp

end

end RHTower
