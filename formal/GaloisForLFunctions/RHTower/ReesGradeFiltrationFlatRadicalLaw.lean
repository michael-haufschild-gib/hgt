import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesJetStability

/-!
# The Rees grade filtration and its flat radical

The Rees grade of a germ measures how badly it may blow up against the inverse powers of a
reference scale `a`.  This module proves that, for a scale which is eventually positive and at
most one, the germs of finite Rees grade form a filtered `ℝ`-algebra: each grade is closed under
sums and scalar multiples, grades increase with the exponent, and a product adds grades.  The
all-orders-flat germs sit inside grade zero and absorb multiplication by the whole algebra, so
they are an ideal of it; when the scale tends to zero along a nontrivial filter the ideal is
proper and the filtration is strictly increasing at every step.

The filtration is inhabited at every grade: every germ that is bounded along the filter has every
finite grade, hence so does every bounded family of continuous linear maps, and a scalar family of
prescribed inverse-power growth realizes a grade exactly.  This is what makes the no-sewing
statements about finite-Rees-grade operators statements about a nonempty, strictly growing class
rather than vacuous ones.
-/

open Filter Asymptotics

namespace RHTower

noncomputable section

variable {α : Type*} {l : Filter α} {a : α → ℝ}

/-! ## Grade zero, and the flat radical inside it -/

/-- Grade zero is exactly boundedness along the filter. -/
theorem reesGradeAtMost_zero_iff {E : Type*} [SeminormedAddCommGroup E] (f : α → E) :
    ReesGradeAtMost l a 0 f ↔ f =O[l] fun _ => (1 : ℝ) := by
  simp only [ReesGradeAtMost, pow_zero]

/-- An all-orders-flat germ is bounded, hence of grade zero. -/
theorem ReesAllOrdersFlat.reesGradeAtMost_zero {E : Type*} [SeminormedAddCommGroup E]
    {f : α → E} (hf : ReesAllOrdersFlat l a f) :
    ReesGradeAtMost l a 0 f := by
  have h := (hf 0).isBigO
  simp only [pow_zero] at h
  simpa only [reesGradeAtMost_zero_iff] using h

/-! ## The reference bound supplied by a contracting scale -/

/-- On a scale which is eventually positive and at most one, every inverse power dominates the
constant germ. -/
theorem isBigO_one_inv_pow (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1) (K : ℕ) :
    (fun _ : α => (1 : ℝ)) =O[l] fun x => (a x)⁻¹ ^ K := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hscale] with x hx
  have h1 : (1 : ℝ) ≤ (a x)⁻¹ := one_le_inv_iff₀.mpr ⟨hx.1, hx.2⟩
  have hK : (1 : ℝ) ≤ (a x)⁻¹ ^ K := one_le_pow₀ h1
  rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hK)]
  exact hK

/-- On a contracting scale a bounded germ has every finite Rees grade. -/
theorem reesGradeAtMost_of_isBigO_one {E : Type*} [SeminormedAddCommGroup E] {f : α → E}
    (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1)
    (hf : f =O[l] fun _ => (1 : ℝ)) (K : ℕ) :
    ReesGradeAtMost l a K f :=
  hf.trans (isBigO_one_inv_pow hscale K)

/-- On a contracting scale an all-orders-flat germ has every finite Rees grade. -/
theorem ReesAllOrdersFlat.reesGradeAtMost {E : Type*} [SeminormedAddCommGroup E]
    {f : α → E} (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1)
    (hf : ReesAllOrdersFlat l a f) (K : ℕ) :
    ReesGradeAtMost l a K f :=
  reesGradeAtMost_of_isBigO_one hscale
    ((reesGradeAtMost_zero_iff f).mp hf.reesGradeAtMost_zero) K

/-! ## The filtration -/

/-- The Rees grades increase with the exponent. -/
theorem reesGradeAtMost_mono {E : Type*} [SeminormedAddCommGroup E] {f : α → E} {K L : ℕ}
    (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1) (hKL : K ≤ L)
    (hf : ReesGradeAtMost l a K f) :
    ReesGradeAtMost l a L f := by
  refine hf.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [hscale] with x hx
  have h1 : (1 : ℝ) ≤ (a x)⁻¹ := one_le_inv_iff₀.mpr ⟨hx.1, hx.2⟩
  have hmono : (a x)⁻¹ ^ K ≤ (a x)⁻¹ ^ L := pow_le_pow_right₀ h1 hKL
  have hKnn : (0 : ℝ) ≤ (a x)⁻¹ ^ K := le_trans zero_le_one (one_le_pow₀ h1)
  have hLnn : (0 : ℝ) ≤ (a x)⁻¹ ^ L := le_trans zero_le_one (one_le_pow₀ h1)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hKnn, abs_of_nonneg hLnn]
  exact hmono

/-- Each Rees grade is closed under sums. -/
theorem reesGradeAtMost_add {E : Type*} [SeminormedAddCommGroup E] {f g : α → E} {K : ℕ}
    (hf : ReesGradeAtMost l a K f) (hg : ReesGradeAtMost l a K g) :
    ReesGradeAtMost l a K (fun x => f x + g x) :=
  hf.add hg

/-- Each Rees grade is closed under scalar multiples. -/
theorem reesGradeAtMost_const_mul {f : α → ℝ} {K : ℕ} (c : ℝ)
    (hf : ReesGradeAtMost l a K f) :
    ReesGradeAtMost l a K (fun x => c * f x) :=
  hf.const_mul_left c

/-- A product of germs adds Rees grades. -/
theorem reesGradeAtMost_mul {f g : α → ℝ} {K L : ℕ}
    (hf : ReesGradeAtMost l a K f) (hg : ReesGradeAtMost l a L g) :
    ReesGradeAtMost l a (K + L) (fun x => f x * g x) := by
  refine (Asymptotics.IsBigO.mul hf hg).congr' EventuallyEq.rfl ?_
  filter_upwards [] with x
  rw [← pow_add]

/-- The exact inverse power realizes its own grade. -/
theorem reesGradeAtMost_inv_pow (K : ℕ) :
    ReesGradeAtMost l a K (fun x => (a x)⁻¹ ^ K) :=
  isBigO_refl _ _

/-! ## The flat radical is an ideal -/

/-- All-orders flatness is closed under sums. -/
theorem ReesAllOrdersFlat.add {E : Type*} [SeminormedAddCommGroup E] {f g : α → E}
    (hf : ReesAllOrdersFlat l a f) (hg : ReesAllOrdersFlat l a g) :
    ReesAllOrdersFlat l a (fun x => f x + g x) :=
  fun N => (hf N).add (hg N)

/-- All-orders flatness is closed under scalar multiples. -/
theorem ReesAllOrdersFlat.const_mul {f : α → ℝ} (c : ℝ) (hf : ReesAllOrdersFlat l a f) :
    ReesAllOrdersFlat l a (fun x => c * f x) :=
  fun N => (hf N).const_mul_left c

/-! ## Properness and strictness, on a scale that tends to zero -/

/-- On a nontrivial filter along which an eventually positive scale tends to zero, the constant
germ one is not all-orders flat: the ideal of flat germs is proper. -/
theorem not_reesAllOrdersFlat_one [l.NeBot]
    (hpos : ∀ᶠ x in l, 0 < a x) (htend : Tendsto a l (nhds 0)) :
    ¬ ReesAllOrdersFlat l a (fun _ : α => (1 : ℝ)) := by
  intro hflat
  have hbound := (hflat 1).bound (c := 1) one_pos
  have hsmall : ∀ᶠ x in l, a x < 1 := htend.eventually (eventually_lt_nhds one_pos)
  obtain ⟨x, ⟨hbx, hpx⟩, hsx⟩ := ((hbound.and hpos).and hsmall).exists
  rw [norm_one, pow_one, one_mul, Real.norm_eq_abs, abs_of_pos hpx] at hbx
  linarith

/-- The Rees filtration is strictly increasing at every step: the inverse power of exponent
`K + 1` does not have grade `K`. -/
theorem not_reesGradeAtMost_inv_pow_succ [l.NeBot]
    (hpos : ∀ᶠ x in l, 0 < a x) (htend : Tendsto a l (nhds 0)) (K : ℕ) :
    ¬ ReesGradeAtMost l a K (fun x => (a x)⁻¹ ^ (K + 1)) := by
  intro h
  rw [ReesGradeAtMost, isBigO_iff] at h
  obtain ⟨c, hc⟩ := h
  have hcpos : (0 : ℝ) < |c| + 1 := by positivity
  have hsmall : ∀ᶠ x in l, a x < (|c| + 1)⁻¹ :=
    htend.eventually (eventually_lt_nhds (by positivity))
  obtain ⟨x, ⟨hcx, hpx⟩, hsx⟩ := ((hc.and hpos).and hsmall).exists
  have hupos : (0 : ℝ) < (a x)⁻¹ := inv_pos.mpr hpx
  have hupow : (0 : ℝ) < (a x)⁻¹ ^ K := pow_pos hupos K
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hupos (K + 1)),
    abs_of_pos hupow, pow_succ, mul_comm c ((a x)⁻¹ ^ K)] at hcx
  have hle : (a x)⁻¹ ≤ c := le_of_mul_le_mul_left hcx hupow
  have hinv : a x * (a x)⁻¹ = 1 := mul_inv_cancel₀ hpx.ne'
  have hmul : a x * (|c| + 1) < 1 := by
    have := (mul_lt_mul_of_pos_right hsx hcpos)
    rwa [inv_mul_cancel₀ hcpos.ne'] at this
  have hgt : |c| + 1 < (a x)⁻¹ := by nlinarith
  have : c ≤ |c| := le_abs_self c
  linarith

/-! ## Inhabitation of the operator grades -/

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- A family of continuous linear maps with bounded norm has every finite operator Rees grade. -/
theorem reesOperatorGradeAtMost_of_isBigO_one {R : α → (E →L[ℝ] F)}
    (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1)
    (hR : (fun x => ‖R x‖) =O[l] fun _ => (1 : ℝ)) (K : ℕ) :
    ReesOperatorGradeAtMost l a K R :=
  reesGradeAtMost_of_isBigO_one hscale hR K

/-- A constant family of continuous linear maps has every finite operator Rees grade. -/
theorem reesOperatorGradeAtMost_const (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1)
    (T : E →L[ℝ] F) (K : ℕ) :
    ReesOperatorGradeAtMost l a K (fun _ => T) := by
  refine reesOperatorGradeAtMost_of_isBigO_one hscale (IsBigO.of_bound ‖T‖ ?_) K
  filter_upwards [] with x
  rw [norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]

/-- The zero family has every finite operator Rees grade. -/
theorem reesOperatorGradeAtMost_zero (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1) (K : ℕ) :
    ReesOperatorGradeAtMost l a K (fun _ : α => (0 : E →L[ℝ] F)) :=
  reesOperatorGradeAtMost_const hscale 0 K

/-- Scaling a fixed operator by a germ of grade `K` gives an operator family of grade `K`. -/
theorem reesOperatorGradeAtMost_smul_const {c : α → ℝ} {K : ℕ} (T : E →L[ℝ] F)
    (hc : ReesGradeAtMost l a K c) :
    ReesOperatorGradeAtMost l a K (fun x => c x • T) := by
  refine (hc.norm_left.const_mul_left ‖T‖).congr' ?_ EventuallyEq.rfl
  filter_upwards [] with x
  rw [norm_smul, mul_comm]

/-- The operator grades are inhabited at every level by a family of prescribed inverse-power
growth. -/
theorem reesOperatorGradeAtMost_inv_pow_smul_const (T : E →L[ℝ] F) (K : ℕ) :
    ReesOperatorGradeAtMost l a K (fun x => (a x)⁻¹ ^ K • T) :=
  reesOperatorGradeAtMost_smul_const T (reesGradeAtMost_inv_pow K)

/-! ## The filtered-algebra law -/

/-- **Rees grade filtration law.**  On a scale which is eventually positive, at most one, and
tends to zero along a nontrivial filter: the finite-grade germs form a filtration closed under
sums, scalar multiples and products with additive grades; the all-orders-flat germs lie in grade
zero, are closed under the algebra action, and form a proper ideal; and the filtration is strictly
increasing, so each grade is inhabited by a germ that the previous grade excludes. -/
theorem reesGradeFiltration_law [l.NeBot]
    (hscale : ∀ᶠ x in l, 0 < a x ∧ a x ≤ 1) (htend : Tendsto a l (nhds 0)) :
    (∀ (K L : ℕ) (f : α → ℝ), K ≤ L → ReesGradeAtMost l a K f →
        ReesGradeAtMost l a L f) ∧
      (∀ (K L : ℕ) (f g : α → ℝ), ReesGradeAtMost l a K f → ReesGradeAtMost l a L g →
        ReesGradeAtMost l a (K + L) (fun x => f x * g x)) ∧
      (∀ (K : ℕ) (r f : α → ℝ), ReesGradeAtMost l a K r → ReesAllOrdersFlat l a f →
        ReesAllOrdersFlat l a (fun x => r x * f x)) ∧
      (¬ ReesAllOrdersFlat l a (fun _ : α => (1 : ℝ))) ∧
      (∀ K : ℕ, ReesGradeAtMost l a (K + 1) (fun x => (a x)⁻¹ ^ (K + 1)) ∧
        ¬ ReesGradeAtMost l a K (fun x => (a x)⁻¹ ^ (K + 1))) := by
  have hpos : ∀ᶠ x in l, 0 < a x := hscale.mono fun _ hx => hx.1
  refine ⟨fun K L f hKL hf => reesGradeAtMost_mono hscale hKL hf, fun K L f g hf hg =>
    reesGradeAtMost_mul hf hg, fun K r f hr hf =>
      reesAllOrdersFlat_mul_reesGradeAtMost l a r f K (hpos.mono fun _ hx => hx.ne') hr hf,
    not_reesAllOrdersFlat_one hpos htend, fun K =>
      ⟨reesGradeAtMost_inv_pow (K + 1), not_reesGradeAtMost_inv_pow_succ hpos htend K⟩⟩

end

end RHTower
