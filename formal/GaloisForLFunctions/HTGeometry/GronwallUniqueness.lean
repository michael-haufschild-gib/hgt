import Mathlib
import GaloisForLFunctions.HTGeometry.IsolatedZeroFinite

/-!
# Grönwall uniqueness for a nonnegative energy

A nonnegative quantity that vanishes at the left endpoint and whose derivative is dominated by a
multiple of itself vanishes identically: `E exp(-K x)` is antitone, nonnegative, and zero at the
left endpoint.

This is the uniqueness half of the Cauchy problem in the only form the Sturm theory needs: a
solution of a second-order linear equation with a double zero vanishes identically, so the zeros of
a nontrivial solution are simple.
-/

noncomputable section

open Set

namespace HTGeometry

/-- **Grönwall uniqueness.**  A nonnegative energy vanishing at the left endpoint and obeying
`E' ≤ K E` vanishes on the whole interval. -/
theorem eq_zero_of_nonneg_of_deriv_le_mul {E E' : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hE : ∀ x ∈ Icc a b, HasDerivAt E (E' x) x)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ E x)
    (hle : ∀ x ∈ Icc a b, E' x ≤ K * E x)
    (h0 : E a = 0) :
    ∀ x ∈ Icc a b, E x = 0 := by
  set G : ℝ → ℝ := fun x => E x * Real.exp (-K * x) with hGdef
  have hGd : ∀ x ∈ Icc a b, HasDerivAt G
      (E' x * Real.exp (-K * x) + E x * (Real.exp (-K * x) * -K)) x := by
    intro x hx
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-K * t)) (Real.exp (-K * x) * -K) x := by
      have hlin : HasDerivAt (fun t : ℝ => -K * t) (-K) x := by
        simpa using (hasDerivAt_id x).const_mul (-K)
      exact hlin.exp
    exact (hE x hx).mul hexp
  have hnonpos : ∀ x ∈ Ioo a b, deriv G x ≤ 0 := by
    intro x hx
    have hxI : x ∈ Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hexppos : 0 < Real.exp (-K * x) := Real.exp_pos _
    rw [(hGd x hxI).deriv]
    nlinarith [hle x hxI, hexppos, hnn x hxI]
  have hcont : ContinuousOn G (Icc a b) :=
    fun x hx => ((hGd x hx).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun x hx => ((hGd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).differentiableAt
      ).differentiableWithinAt
  have hanti : AntitoneOn G (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff
    rw [interior_Icc]
    exact hnonpos
  intro x hx
  have hGa : G a = 0 := by rw [hGdef]; simp [h0]
  have hGle : G x ≤ G a := hanti (left_mem_Icc.mpr hab) hx hx.1
  have hGnn : 0 ≤ G x := by
    rw [hGdef]
    exact mul_nonneg (hnn x hx) (Real.exp_pos _).le
  have hGx : G x = 0 := le_antisymm (by rw [hGa] at hGle; exact hGle) hGnn
  have hexppos : (0 : ℝ) < Real.exp (-K * x) := Real.exp_pos _
  rw [hGdef] at hGx
  simp only at hGx
  exact (mul_eq_zero.mp hGx).resolve_right (ne_of_gt hexppos)

/-- **A double zero forces the energy to vanish to the right.**  Stated for the energy of a
second-order equation: `E = u² + (u')²`. -/
theorem sq_add_sq_eq_zero_of_double_zero {u Du DDu : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (Du x) x)
    (hDu : ∀ x ∈ Icc a b, HasDerivAt Du (DDu x) x)
    (hbound : ∀ x ∈ Icc a b, |DDu x| ≤ K * (|u x| + |Du x|))
    (hK : 0 ≤ K) (hu0 : u a = 0) (hDu0 : Du a = 0) :
    ∀ x ∈ Icc a b, u x = 0 ∧ Du x = 0 := by
  set E : ℝ → ℝ := fun x => u x ^ 2 + Du x ^ 2 with hEdef
  set E' : ℝ → ℝ := fun x => 2 * u x * Du x + 2 * Du x * DDu x with hE'def
  have hEd : ∀ x ∈ Icc a b, HasDerivAt E (E' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => u t ^ 2) (2 * u x * Du x) x := by
      have h := (hu x hx).pow 2
      have hv : ((2 : ℕ) : ℝ) * u x ^ (2 - 1) * Du x = 2 * u x * Du x := by norm_num
      rw [hv] at h
      exact h
    have h2 : HasDerivAt (fun t : ℝ => Du t ^ 2) (2 * Du x * DDu x) x := by
      have h := (hDu x hx).pow 2
      have hv : ((2 : ℕ) : ℝ) * Du x ^ (2 - 1) * DDu x = 2 * Du x * DDu x := by norm_num
      rw [hv] at h
      exact h
    exact h1.add h2
  have hnn : ∀ x ∈ Icc a b, 0 ≤ E x := by
    intro x _
    rw [hEdef]
    positivity
  have hle : ∀ x ∈ Icc a b, E' x ≤ (2 + 3 * K) * E x := by
    intro x hx
    have hb := hbound x hx
    have h1 : 2 * u x * Du x ≤ u x ^ 2 + Du x ^ 2 := by
      nlinarith [sq_nonneg (u x - Du x)]
    have h2 : 2 * Du x * DDu x ≤ 2 * |Du x| * (K * (|u x| + |Du x|)) := by
      have habs : Du x * DDu x ≤ |Du x| * |DDu x| := by
        calc Du x * DDu x ≤ |Du x * DDu x| := le_abs_self _
          _ = |Du x| * |DDu x| := abs_mul _ _
      nlinarith [abs_nonneg (Du x), hb, habs]
    have h3 : 2 * |Du x| * (K * (|u x| + |Du x|)) ≤ 3 * K * (u x ^ 2 + Du x ^ 2) := by
      have hu2 : |u x| ^ 2 = u x ^ 2 := sq_abs _
      have hd2 : |Du x| ^ 2 = Du x ^ 2 := sq_abs _
      nlinarith [mul_nonneg hK (sq_nonneg (|u x| - |Du x|)),
        mul_nonneg hK (sq_nonneg (|u x|)), abs_nonneg (u x), abs_nonneg (Du x), hK,
        hu2, hd2]
    rw [hE'def, hEdef]
    simp only
    nlinarith [h1, h2, h3, sq_nonneg (u x), sq_nonneg (Du x), hK]
  have h0 : E a = 0 := by rw [hEdef]; simp [hu0, hDu0]
  intro x hx
  have hEx := eq_zero_of_nonneg_of_deriv_le_mul hab hEd hnn hle h0 x hx
  rw [hEdef] at hEx
  simp only at hEx
  constructor
  · nlinarith [sq_nonneg (u x), sq_nonneg (Du x), hEx]
  · nlinarith [sq_nonneg (u x), sq_nonneg (Du x), hEx]

/-- **Grönwall uniqueness, backwards.**  A nonnegative energy vanishing at the *right* endpoint and
obeying `-(K E) ≤ E'` vanishes on the whole interval. -/
theorem eq_zero_of_nonneg_of_neg_mul_le_deriv {E E' : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hE : ∀ x ∈ Icc a b, HasDerivAt E (E' x) x)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ E x)
    (hge : ∀ x ∈ Icc a b, -(K * E x) ≤ E' x)
    (h0 : E b = 0) :
    ∀ x ∈ Icc a b, E x = 0 := by
  set G : ℝ → ℝ := fun x => E x * Real.exp (K * x) with hGdef
  have hGd : ∀ x ∈ Icc a b, HasDerivAt G
      (E' x * Real.exp (K * x) + E x * (Real.exp (K * x) * K)) x := by
    intro x hx
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (K * t)) (Real.exp (K * x) * K) x := by
      have hlin : HasDerivAt (fun t : ℝ => K * t) K x := by
        simpa using (hasDerivAt_id x).const_mul K
      exact hlin.exp
    exact (hE x hx).mul hexp
  have hnonneg : ∀ x ∈ Ioo a b, 0 ≤ deriv G x := by
    intro x hx
    have hxI : x ∈ Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hexppos : 0 < Real.exp (K * x) := Real.exp_pos _
    rw [(hGd x hxI).deriv]
    nlinarith [hge x hxI, hexppos, hnn x hxI]
  have hcont : ContinuousOn G (Icc a b) :=
    fun x hx => ((hGd x hx).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun x hx => ((hGd x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).differentiableAt
      ).differentiableWithinAt
  have hmono : MonotoneOn G (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff
    rw [interior_Icc]
    exact hnonneg
  intro x hx
  have hGb : G b = 0 := by rw [hGdef]; simp [h0]
  have hGle : G x ≤ G b := hmono hx (right_mem_Icc.mpr hab) hx.2
  have hGnn : 0 ≤ G x := by
    rw [hGdef]
    exact mul_nonneg (hnn x hx) (Real.exp_pos _).le
  have hGx : G x = 0 := le_antisymm (by rw [hGb] at hGle; exact hGle) hGnn
  have hexppos : (0 : ℝ) < Real.exp (K * x) := Real.exp_pos _
  rw [hGdef] at hGx
  simp only at hGx
  exact (mul_eq_zero.mp hGx).resolve_right (ne_of_gt hexppos)

/-- **A double zero anywhere kills the solution on the whole interval.** -/
theorem eq_zero_of_double_zero_interior {u Du DDu : ℝ → ℝ} {a b K x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc a b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (Du x) x)
    (hDu : ∀ x ∈ Icc a b, HasDerivAt Du (DDu x) x)
    (hbound : ∀ x ∈ Icc a b, |DDu x| ≤ K * (|u x| + |Du x|))
    (hK : 0 ≤ K) (hu0 : u x₀ = 0) (hDu0 : Du x₀ = 0) :
    ∀ x ∈ Icc a b, u x = 0 := by
  have hright : ∀ x ∈ Icc x₀ b, u x = 0 := by
    intro x hx
    have hsub : Icc x₀ b ⊆ Icc a b := Icc_subset_Icc hx₀.1 le_rfl
    exact (sq_add_sq_eq_zero_of_double_zero hx₀.2 (fun y hy => hu y (hsub hy))
      (fun y hy => hDu y (hsub hy)) (fun y hy => hbound y (hsub hy)) hK hu0 hDu0 x hx).1
  have hleft : ∀ x ∈ Icc a x₀, u x = 0 := by
    have hsub : Icc a x₀ ⊆ Icc a b := Icc_subset_Icc le_rfl hx₀.2
    set E : ℝ → ℝ := fun x => u x ^ 2 + Du x ^ 2 with hEdef
    set E' : ℝ → ℝ := fun x => 2 * u x * Du x + 2 * Du x * DDu x with hE'def
    have hEd : ∀ x ∈ Icc a x₀, HasDerivAt E (E' x) x := by
      intro x hx
      have h1 : HasDerivAt (fun t : ℝ => u t ^ 2) (2 * u x * Du x) x := by
        have h := (hu x (hsub hx)).pow 2
        have hv : ((2 : ℕ) : ℝ) * u x ^ (2 - 1) * Du x = 2 * u x * Du x := by norm_num
        rw [hv] at h
        exact h
      have h2 : HasDerivAt (fun t : ℝ => Du t ^ 2) (2 * Du x * DDu x) x := by
        have h := (hDu x (hsub hx)).pow 2
        have hv : ((2 : ℕ) : ℝ) * Du x ^ (2 - 1) * DDu x = 2 * Du x * DDu x := by norm_num
        rw [hv] at h
        exact h
      exact h1.add h2
    have hnn : ∀ x ∈ Icc a x₀, 0 ≤ E x := by
      intro x _
      rw [hEdef]
      positivity
    have hge : ∀ x ∈ Icc a x₀, -((2 + 3 * K) * E x) ≤ E' x := by
      intro x hx
      have hb := hbound x (hsub hx)
      have h1 : -(u x ^ 2 + Du x ^ 2) ≤ 2 * u x * Du x := by
        nlinarith [sq_nonneg (u x + Du x)]
      have h2 : -(2 * |Du x| * (K * (|u x| + |Du x|))) ≤ 2 * Du x * DDu x := by
        have habs : -(|Du x| * |DDu x|) ≤ Du x * DDu x := by
          calc -(|Du x| * |DDu x|) = -|Du x * DDu x| := by rw [abs_mul]
            _ ≤ Du x * DDu x := neg_abs_le _
        nlinarith [abs_nonneg (Du x), hb, habs]
      have h3 : 2 * |Du x| * (K * (|u x| + |Du x|)) ≤ 3 * K * (u x ^ 2 + Du x ^ 2) := by
        have hu2 : |u x| ^ 2 = u x ^ 2 := sq_abs _
        have hd2 : |Du x| ^ 2 = Du x ^ 2 := sq_abs _
        nlinarith [mul_nonneg hK (sq_nonneg (|u x| - |Du x|)),
          mul_nonneg hK (sq_nonneg (|u x|)), abs_nonneg (u x), abs_nonneg (Du x), hK,
          hu2, hd2]
      rw [hE'def, hEdef]
      simp only
      nlinarith [h1, h2, h3, sq_nonneg (u x), sq_nonneg (Du x), hK]
    have h0 : E x₀ = 0 := by rw [hEdef]; simp [hu0, hDu0]
    intro x hx
    have hEx := eq_zero_of_nonneg_of_neg_mul_le_deriv hx₀.1 hEd hnn hge h0 x hx
    rw [hEdef] at hEx
    simp only at hEx
    nlinarith [sq_nonneg (u x), sq_nonneg (Du x), hEx]
  intro x hx
  rcases le_or_gt x x₀ with h | h
  · exact hleft x ⟨hx.1, h⟩
  · exact hright x ⟨le_of_lt h, hx.2⟩


/-- **A nontrivial solution has simple zeros.** -/
theorem simple_zeros_of_nontrivial {u Du DDu : ℝ → ℝ} {a b K : ℝ}
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (Du x) x)
    (hDu : ∀ x ∈ Icc a b, HasDerivAt Du (DDu x) x)
    (hbound : ∀ x ∈ Icc a b, |DDu x| ≤ K * (|u x| + |Du x|))
    (hK : 0 ≤ K) (hnt : ∃ y ∈ Icc a b, u y ≠ 0) :
    ∀ x ∈ Icc a b, u x = 0 → Du x ≠ 0 := by
  intro x hx hzero hDzero
  obtain ⟨y, hy, hyne⟩ := hnt
  exact hyne (eq_zero_of_double_zero_interior hx hu hDu hbound hK hzero hDzero y hy)

/-- **A nontrivial solution has finitely many zeros.**  Simplicity plus isolation. -/
theorem finite_zeros_of_nontrivial {u Du DDu : ℝ → ℝ} {a b K : ℝ}
    (huc : Continuous u)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (Du x) x)
    (hDu : ∀ x ∈ Icc a b, HasDerivAt Du (DDu x) x)
    (hbound : ∀ x ∈ Icc a b, |DDu x| ≤ K * (|u x| + |Du x|))
    (hK : 0 ≤ K) (hnt : ∃ y ∈ Icc a b, u y ≠ 0) :
    {x : ℝ | x ∈ Icc a b ∧ u x = 0}.Finite :=
  finite_zeros_of_simple huc hu (simple_zeros_of_nontrivial hu hDu hbound hK hnt)


end HTGeometry
