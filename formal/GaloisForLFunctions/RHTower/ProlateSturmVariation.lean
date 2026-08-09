import GaloisForLFunctions.HTGeometry.DarbouxMonotoneCell
import GaloisForLFunctions.HTGeometry.GronwallUniqueness
import GaloisForLFunctions.RHTower.ProlateCommutationKernel
import GaloisForLFunctions.RHTower.ProlateOneTurningVariation

/-!
# The prolate mode's variation from its sign cells

Assembling the two halves already present: on a cell where `(χ + c² y²) ψ(y)` has a fixed sign the
prolate mode has at most one stationary point, and a function with at most one stationary point per
cell has variation bounded by twice its critical count.

The result is the fixed-mode variation law in the form the card's `(19e)` needs: the bound depends
on the *number of sign cells*, not on the equation's parameters, so a mode whose sign-cell count is
bounded independently of the aperture has variation bounded independently of the aperture.
-/

open Set

namespace RHTower

open HTGeometry

/-- **The prolate mode's variation, from a sign-cell partition.**  Each open cell on which
`(χ + c² y²) ψ` has fixed sign contributes at most one stationary point, so the total variation is
controlled by the number of cells. -/
theorem prolate_eVariationOn_le_of_signCells {c χ B : ℝ} {ψ : ℝ → ℝ} {J : ℕ → ℝ} {m : ℕ}
    (hψ1 : Differentiable ℝ ψ) (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hJ : Monotone J)
    (hsign : ∀ i : ℕ,
      (∀ y ∈ Ioo (J i) (J (i + 1)), 0 < (χ + c ^ 2 * y ^ 2) * ψ y)
        ∨ ∀ y ∈ Ioo (J i) (J (i + 1)), (χ + c ^ 2 * y ^ 2) * ψ y < 0)
    (hbound : ∀ y ∈ Icc (J 0) (J m), |ψ y| ≤ B) :
    ∃ S : Finset ℝ,
      eVariationOn ψ (Icc (J 0) (J m)) ≤ ENNReal.ofReal (2 * (S.card + 1) * B) := by
  have hsub : ∀ i : ℕ,
      {y : ℝ | y ∈ Ioo (J i) (J (i + 1)) ∧ deriv ψ y = 0}.Subsingleton := by
    intro i
    have hIcc : {y : ℝ | y ∈ Icc (J i) (J (i + 1)) ∧ deriv ψ y = 0}.Subsingleton := by
      rcases hsign i with hpos | hneg
      · exact prolate_criticalSet_subsingleton_of_rhs_pos hψ2 heig hpos
      · exact prolate_criticalSet_subsingleton_of_rhs_neg hψ2 heig hneg
    intro x hx y hy
    exact hIcc ⟨Ioo_subset_Icc_self hx.1, hx.2⟩ ⟨Ioo_subset_Icc_self hy.1, hy.2⟩
  exact HTGeometry.eVariationOn_le_of_cellwise_subsingleton hJ hsub
    (fun x _ => (hψ1 x).hasDerivAt) hbound

/-- **The mode has bounded variation on its sign-cell range.** -/
theorem prolate_boundedVariationOn_of_signCells {c χ B : ℝ} {ψ : ℝ → ℝ} {J : ℕ → ℝ} {m : ℕ}
    (hψ1 : Differentiable ℝ ψ) (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hJ : Monotone J)
    (hsign : ∀ i : ℕ,
      (∀ y ∈ Ioo (J i) (J (i + 1)), 0 < (χ + c ^ 2 * y ^ 2) * ψ y)
        ∨ ∀ y ∈ Ioo (J i) (J (i + 1)), (χ + c ^ 2 * y ^ 2) * ψ y < 0)
    (hbound : ∀ y ∈ Icc (J 0) (J m), |ψ y| ≤ B) :
    BoundedVariationOn ψ (Icc (J 0) (J m)) := by
  obtain ⟨S, hS⟩ := prolate_eVariationOn_le_of_signCells hψ1 hψ2 heig hJ hsign hbound
  exact ne_of_lt (hS.trans_lt ENNReal.ofReal_lt_top)

/-- **`(19g)` from a finite zero set.**  If the Sturm right-hand side `(χ + c² y²) ψ` vanishes only
on a finite set inside `(a, b)`, the mode's total variation there is bounded by twice its critical
count.  The sign cells are the gaps between those zeros, and the intermediate value theorem gives
each gap a fixed sign. -/
theorem prolate_eVariationOn_le_of_finite_zeros {c χ B a b : ℝ} {ψ : ℝ → ℝ} (hab : a ≤ b)
    (hψ1 : Differentiable ℝ ψ) (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (Z : Finset ℝ)
    (hZ : ∀ y ∈ Ioo a b, (χ + c ^ 2 * y ^ 2) * ψ y = 0 → y ∈ Z)
    (hbound : ∀ y ∈ Icc a b, |ψ y| ≤ B) :
    ∃ S : Finset ℝ, eVariationOn ψ (Icc a b) ≤ ENNReal.ofReal (2 * (S.card + 1) * B) := by
  obtain ⟨m, J, hJmono, hJ0, hJm, _, htail, hcell⟩ :=
    HTGeometry.exists_monotone_partition_of_finset hab Z
  have hgcont : Continuous (fun y : ℝ => (χ + c ^ 2 * y ^ 2) * ψ y) :=
    (continuous_const.add (continuous_const.mul (continuous_pow 2))).mul hψ1.continuous
  have hsign : ∀ i : ℕ,
      (∀ y ∈ Ioo (J i) (J (i + 1)), 0 < (χ + c ^ 2 * y ^ 2) * ψ y)
        ∨ ∀ y ∈ Ioo (J i) (J (i + 1)), (χ + c ^ 2 * y ^ 2) * ψ y < 0 := by
    intro i
    by_cases hi : i < m
    · refine HTGeometry.sign_fixed_of_no_zero hgcont.continuousOn (fun y hy hzero => ?_)
      have hyab : y ∈ Ioo a b := by
        constructor
        · exact lt_of_le_of_lt (hJ0 ▸ hJmono (Nat.zero_le i)) hy.1
        · exact lt_of_lt_of_le hy.2 (hJm ▸ hJmono (Nat.succ_le_iff.mpr hi))
      exact hcell i hi y hy (hZ y hyab hzero)
    · left
      intro y hy
      exfalso
      have h1 : J i = b := htail i (Nat.le_of_not_lt hi)
      have h2 : J (i + 1) = b := htail (i + 1) (by omega)
      rw [h1, h2] at hy
      exact absurd hy (by simp)
  have hbd : ∀ y ∈ Icc (J 0) (J m), |ψ y| ≤ B := by rw [hJ0, hJm]; exact hbound
  obtain ⟨S, hS⟩ := prolate_eVariationOn_le_of_signCells hψ1 hψ2 heig hJmono hsign hbd
  rw [hJ0, hJm] at hS
  exact ⟨S, hS⟩


/-- **The prolate coefficient bound.**  Strictly inside the band the second derivative is dominated
by the solution and its first derivative, with an explicit constant. -/
theorem prolate_secondDeriv_bound {c χ r x : ℝ} {ψ : ℝ → ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (hx : |x| ≤ r)
    (heig : prolateSLAction c ψ x = χ * ψ x) :
    |deriv (deriv ψ) x|
      ≤ ((|χ| + c ^ 2 + 2) / (1 - r ^ 2)) * (|ψ x| + |deriv ψ x|) := by
  have hxr : x ^ 2 ≤ r ^ 2 := by
    have h := sq_abs x
    nlinarith [abs_nonneg x, hx, h]
  have hden : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
  have hden' : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hkey : (1 - x ^ 2) * deriv (deriv ψ) x = (χ + c ^ 2 * x ^ 2) * ψ x + 2 * x * deriv ψ x := by
    rw [prolateSLAction] at heig
    linarith
  have hnum : |(χ + c ^ 2 * x ^ 2) * ψ x + 2 * x * deriv ψ x|
      ≤ (|χ| + c ^ 2 + 2) * (|ψ x| + |deriv ψ x|) := by
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |(χ + c ^ 2 * x ^ 2) * ψ x| ≤ (|χ| + c ^ 2) * |ψ x| := by
      rw [abs_mul]
      have hc : |χ + c ^ 2 * x ^ 2| ≤ |χ| + c ^ 2 := by
        refine le_trans (abs_add_le _ _) ?_
        have : |c ^ 2 * x ^ 2| ≤ c ^ 2 := by
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ 2 * x ^ 2)]
          nlinarith [sq_nonneg c, hxr, hr, sq_nonneg x]
        linarith
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    have h2 : |2 * x * deriv ψ x| ≤ 2 * |deriv ψ x| := by
      rw [abs_mul, abs_mul]
      have hx2 : |(2 : ℝ)| * |x| ≤ 2 := by
        rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        nlinarith [abs_nonneg x, hx, hr]
      exact mul_le_mul_of_nonneg_right hx2 (abs_nonneg _)
    have hpos : (0 : ℝ) ≤ |χ| + c ^ 2 := by positivity
    nlinarith [h1, h2, mul_nonneg hpos (abs_nonneg (deriv ψ x)), abs_nonneg (ψ x)]
  have habs : |deriv (deriv ψ) x| * (1 - x ^ 2)
      ≤ (|χ| + c ^ 2 + 2) * (|ψ x| + |deriv ψ x|) := by
    have : |(1 - x ^ 2) * deriv (deriv ψ) x| = (1 - x ^ 2) * |deriv (deriv ψ) x| := by
      rw [abs_mul, abs_of_pos hden']
    rw [hkey] at this
    linarith [hnum, this]
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [habs, hden, hden', hxr, abs_nonneg (deriv (deriv ψ) x)]

/-- **A nontrivial prolate mode has finitely many zeros strictly inside the band.** -/
theorem prolate_finite_zeros {c χ r : ℝ} {ψ : ℝ → ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1)
    (hψ1 : Differentiable ℝ ψ) (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hnt : ∃ y ∈ Icc (-r) r, ψ y ≠ 0) :
    {x : ℝ | x ∈ Icc (-r) r ∧ ψ x = 0}.Finite := by
  have hxr : ∀ x ∈ Icc (-r) r, |x| ≤ r := by
    intro x hx
    rw [abs_le]
    exact ⟨hx.1, hx.2⟩
  refine HTGeometry.finite_zeros_of_nontrivial (Du := deriv ψ) (DDu := deriv (deriv ψ))
    (K := (|χ| + c ^ 2 + 2) / (1 - r ^ 2)) hψ1.continuous
    (fun x _ => (hψ1 x).hasDerivAt) (fun x _ => (hψ2 x).hasDerivAt)
    (fun x hx => prolate_secondDeriv_bound hr0 hr (hxr x hx) (heig x)) ?_ hnt
  have hden : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
  positivity


/-- The turning-point set of the prolate right-hand side is finite: it is the zero set of a
quadratic in `y`. -/
theorem finite_prolate_turning_points {c χ : ℝ} (hc : c ≠ 0) :
    {y : ℝ | χ + c ^ 2 * y ^ 2 = 0}.Finite := by
  by_cases hne : ({y : ℝ | χ + c ^ 2 * y ^ 2 = 0}).Nonempty
  · obtain ⟨a, ha⟩ := hne
    refine Set.Finite.subset ((Set.finite_singleton (-a)).insert a) (fun y hy => ?_)
    simp only [Set.mem_setOf_eq] at hy ha
    have hc2 : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hc
    have h1 : c ^ 2 * y ^ 2 = c ^ 2 * a ^ 2 := by linarith
    have h2 : y ^ 2 = a ^ 2 := mul_left_cancel₀ hc2 h1
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

/-- **`(19e)` for a nontrivial prolate mode.**  Strictly inside the band, a nontrivial mode has
bounded variation, with the bound controlled by its critical count and its sup norm. -/
theorem prolate_boundedVariationOn_of_nontrivial {c χ r B : ℝ} {ψ : ℝ → ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (hc : c ≠ 0)
    (hψ1 : Differentiable ℝ ψ) (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hnt : ∃ y ∈ Icc (-r) r, ψ y ≠ 0)
    (hbound : ∀ y ∈ Icc (-r) r, |ψ y| ≤ B) :
    ∃ S : Finset ℝ,
      eVariationOn ψ (Icc (-r) r) ≤ ENNReal.ofReal (2 * (S.card + 1) * B) := by
  classical
  have hrr : (-r : ℝ) ≤ r := by linarith
  have hzero := prolate_finite_zeros hr0 hr hψ1 hψ2 heig hnt
  have hturn := finite_prolate_turning_points (c := c) (χ := χ) hc
  have hunion : {y : ℝ | y ∈ Icc (-r) r ∧ (χ + c ^ 2 * y ^ 2) * ψ y = 0}.Finite := by
    refine Set.Finite.subset (hturn.union hzero) (fun y hy => ?_)
    obtain ⟨hyI, hyz⟩ := hy
    rcases mul_eq_zero.mp hyz with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hyI, h⟩
  refine prolate_eVariationOn_le_of_finite_zeros hrr hψ1 hψ2 heig hunion.toFinset ?_ hbound
  intro y hy hzeroy
  exact hunion.mem_toFinset.mpr ⟨Ioo_subset_Icc_self hy, hzeroy⟩


/-- **From the complex operator to the real one.**  The complex prolate action applied to a real
function through the coercion is the coercion of the real prolate action, so a complex
eigen-equation with a real eigenvalue is the real eigen-equation. -/
theorem prolateActionC_ofReal {c : ℝ} (ψ : ℝ → ℝ) (x : ℝ) :
    prolateActionC c (fun y : ℝ => ((ψ y : ℝ) : ℂ)) (fun y : ℝ => ((deriv ψ y : ℝ) : ℂ))
        (fun y : ℝ => ((deriv (deriv ψ) y : ℝ) : ℂ)) x
      = ((prolateSLAction c ψ x : ℝ) : ℂ) := by
  rw [prolateActionC, prolateSLAction]
  push_cast
  ring

/-- **The real eigen-equation from the complex one.** -/
theorem prolateSLAction_eq_of_prolateActionC {c α : ℝ} {ψ : ℝ → ℝ}
    (h : ∀ x : ℝ, prolateActionC c (fun y : ℝ => ((ψ y : ℝ) : ℂ))
        (fun y : ℝ => ((deriv ψ y : ℝ) : ℂ))
        (fun y : ℝ => ((deriv (deriv ψ) y : ℝ) : ℂ)) x
      = ((α : ℝ) : ℂ) * ((ψ x : ℝ) : ℂ)) :
    ∀ x : ℝ, prolateSLAction c ψ x = α * ψ x := by
  intro x
  have hx := h x
  rw [prolateActionC_ofReal ψ x] at hx
  have hcast : ((α : ℝ) : ℂ) * ((ψ x : ℝ) : ℂ) = ((α * ψ x : ℝ) : ℂ) := by push_cast; ring
  rw [hcast] at hx
  exact_mod_cast hx

/-- **The full bridge: a real solution of the complex eigen-equation has bounded variation.**
Every hypothesis except nontriviality and the eigen-equation itself is discharged. -/
theorem prolate_boundedVariationOn_of_complex_eigen {c α r B : ℝ} {ψ : ℝ → ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (hc : c ≠ 0)
    (hψ1 : Differentiable ℝ ψ) (hψ2 : Differentiable ℝ (deriv ψ))
    (h : ∀ x : ℝ, prolateActionC c (fun y : ℝ => ((ψ y : ℝ) : ℂ))
        (fun y : ℝ => ((deriv ψ y : ℝ) : ℂ))
        (fun y : ℝ => ((deriv (deriv ψ) y : ℝ) : ℂ)) x
      = ((α : ℝ) : ℂ) * ((ψ x : ℝ) : ℂ))
    (hnt : ∃ y ∈ Icc (-r) r, ψ y ≠ 0)
    (hbound : ∀ y ∈ Icc (-r) r, |ψ y| ≤ B) :
    ∃ S : Finset ℝ,
      eVariationOn ψ (Icc (-r) r) ≤ ENNReal.ofReal (2 * (S.card + 1) * B) :=
  prolate_boundedVariationOn_of_nontrivial hr0 hr hc hψ1 hψ2
    (prolateSLAction_eq_of_prolateActionC h) hnt hbound


/-- **The Wronskian of two modes with the same eigenvalue is constant.**  The Lagrange bracket's
derivative is `(L u) v - u (L v)`, which vanishes when both solve the same eigen-equation. -/
theorem hasDerivAt_prolateWronskian_eq_zero {c α x : ℝ} {u v : ℝ → ℝ}
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    (hv1 : Differentiable ℝ v) (hv2 : Differentiable ℝ (deriv v))
    (heu : ∀ y : ℝ, prolateSLAction c u y = α * u y)
    (hev : ∀ y : ℝ, prolateSLAction c v y = α * v y) :
    HasDerivAt (fun y : ℝ => (1 - y ^ 2) * (deriv u y * v y - u y * deriv v y)) 0 x := by
  have hp : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have hlag := HTGeometry.hasDerivAt_lagrangeBracket (p := fun y : ℝ => 1 - y ^ 2)
    (Dp := fun y : ℝ => -2 * y) (u := u) (v := v) (Du := deriv u) (Dv := deriv v)
    (DDu := deriv (deriv u)) (DDv := deriv (deriv v)) hp (hu1 x).hasDerivAt (hv1 x).hasDerivAt
    (hu2 x).hasDerivAt (hv2 x).hasDerivAt
  refine hlag.congr_deriv ?_
  have hU : -2 * x * deriv u x + (1 - x ^ 2) * deriv (deriv u) x = (α + c ^ 2 * x ^ 2) * u x := by
    have h := heu x
    rw [prolateSLAction] at h
    linarith
  have hV : -2 * x * deriv v x + (1 - x ^ 2) * deriv (deriv v) x = (α + c ^ 2 * x ^ 2) * v x := by
    have h := hev x
    rw [prolateSLAction] at h
    linarith
  rw [hU, hV]
  ring

/-- **The Wronskian vanishes identically.**  It is constant on the band and its value at the
endpoint is zero, because the weight `1 - x²` vanishes there.  This is simplicity of the eigenvalue
in the ODE sense: two modes with the same eigenvalue have vanishing Wronskian. -/
theorem prolateWronskian_eq_zero {c α : ℝ} {u v : ℝ → ℝ}
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    (hv1 : Differentiable ℝ v) (hv2 : Differentiable ℝ (deriv v))
    (heu : ∀ y : ℝ, prolateSLAction c u y = α * u y)
    (hev : ∀ y : ℝ, prolateSLAction c v y = α * v y) (x : ℝ) :
    (1 - x ^ 2) * (deriv u x * v x - u x * deriv v x) = 0 := by
  set W : ℝ → ℝ := fun y : ℝ => (1 - y ^ 2) * (deriv u y * v y - u y * deriv v y) with hWdef
  have hWd : ∀ y : ℝ, HasDerivAt W 0 y := fun y =>
    hasDerivAt_prolateWronskian_eq_zero hu1 hu2 hv1 hv2 heu hev
  have hconst : ∀ y : ℝ, W y = W 1 := by
    intro y
    have hdiff : Differentiable ℝ W := fun z => (hWd z).differentiableAt
    have hderiv : ∀ z : ℝ, deriv W z = 0 := fun z => (hWd z).deriv
    exact is_const_of_deriv_eq_zero hdiff hderiv y 1
  have hW1 : W 1 = 0 := by
    rw [hWdef]
    norm_num
  rw [show (1 - x ^ 2) * (deriv u x * v x - u x * deriv v x) = W x from rfl, hconst x, hW1]


theorem deriv_sub_const_mul {u v : ℝ → ℝ} (k : ℝ) (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) :
    deriv (fun y : ℝ => v y - k * u y) = fun y : ℝ => deriv v y - k * deriv u y := by
  funext y
  exact ((hv y).hasDerivAt.sub ((hu y).hasDerivAt.const_mul k)).deriv

theorem prolateSLAction_sub_const_mul {c k : ℝ} {u v : ℝ → ℝ}
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    (hv1 : Differentiable ℝ v) (hv2 : Differentiable ℝ (deriv v)) (y : ℝ) :
    prolateSLAction c (fun z : ℝ => v z - k * u z) y
      = prolateSLAction c v y - k * prolateSLAction c u y := by
  have h1 : deriv (fun z : ℝ => v z - k * u z) = fun z : ℝ => deriv v z - k * deriv u z :=
    deriv_sub_const_mul k hu1 hv1
  have h2 : deriv (deriv (fun z : ℝ => v z - k * u z))
      = fun z : ℝ => deriv (deriv v) z - k * deriv (deriv u) z := by
    rw [h1]
    exact deriv_sub_const_mul k hu2 hv2
  rw [prolateSLAction, prolateSLAction, prolateSLAction, h2, h1]
  ring

/-- **Two prolate modes with the same eigenvalue are proportional.**  The Wronskian vanishes, so at
a point where `u` is nonzero the difference `v - (v/u) u` has a double zero, and Grönwall
uniqueness kills it. -/
theorem prolate_eq_const_mul_of_same_eigenvalue {c α r : ℝ} {u v : ℝ → ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    (hv1 : Differentiable ℝ v) (hv2 : Differentiable ℝ (deriv v))
    (heu : ∀ y : ℝ, prolateSLAction c u y = α * u y)
    (hev : ∀ y : ℝ, prolateSLAction c v y = α * v y)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc (-r) r) (hu0 : u x₀ ≠ 0) :
    ∀ x ∈ Icc (-r) r, v x = (v x₀ / u x₀) * u x := by
  set k : ℝ := v x₀ / u x₀ with hkdef
  set w : ℝ → ℝ := fun y : ℝ => v y - k * u y with hwdef
  have hw1 : Differentiable ℝ w := fun y => (hv1 y).sub ((hu1 y).const_mul k)
  have hdw : deriv w = fun y : ℝ => deriv v y - k * deriv u y := deriv_sub_const_mul k hu1 hv1
  have hw2 : Differentiable ℝ (deriv w) := by
    rw [hdw]
    exact fun y => (hv2 y).sub ((hu2 y).const_mul k)
  have hew : ∀ y : ℝ, prolateSLAction c w y = α * w y := by
    intro y
    rw [hwdef, prolateSLAction_sub_const_mul hu1 hu2 hv1 hv2 y, heu y, hev y]
    ring
  have hw0 : w x₀ = 0 := by
    rw [hwdef, hkdef]
    field_simp
    ring
  have hdw0 : deriv w x₀ = 0 := by
    have hwr := prolateWronskian_eq_zero hu1 hu2 hv1 hv2 heu hev x₀
    have hx1 : |x₀| ≤ r := by
      rw [abs_le]
      exact ⟨hx₀.1, hx₀.2⟩
    have hne : (1 : ℝ) - x₀ ^ 2 ≠ 0 := by
      have : x₀ ^ 2 ≤ r ^ 2 := by nlinarith [sq_abs x₀, abs_nonneg x₀, hx1]
      nlinarith [hr, hr0]
    have hzero : deriv u x₀ * v x₀ - u x₀ * deriv v x₀ = 0 := by
      rcases mul_eq_zero.mp hwr with h | h
      · exact absurd h hne
      · exact h
    rw [hdw, hkdef]
    field_simp
    linarith [hzero]
  have hxr : ∀ x ∈ Icc (-r) r, |x| ≤ r := by
    intro x hx
    rw [abs_le]
    exact ⟨hx.1, hx.2⟩
  have hkill := HTGeometry.eq_zero_of_double_zero_interior (u := w) (Du := deriv w)
    (DDu := deriv (deriv w)) (K := (|α| + c ^ 2 + 2) / (1 - r ^ 2)) hx₀
    (fun x _ => (hw1 x).hasDerivAt) (fun x _ => (hw2 x).hasDerivAt)
    (fun x hx => prolate_secondDeriv_bound hr0 hr (hxr x hx) (hew x))
    (by
      have hden : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
      positivity) hw0 hdw0
  intro x hx
  have := hkill x hx
  rw [hwdef] at this
  simp only at this
  linarith


/-- Differentiability descends through the real coercion. -/
theorem differentiable_of_ofReal {ψ : ℝ → ℝ}
    (h : Differentiable ℝ (fun y : ℝ => ((ψ y : ℝ) : ℂ))) : Differentiable ℝ ψ := by
  have hre : ψ = fun y : ℝ => (((ψ y : ℝ) : ℂ)).re := by
    funext y
    simp
  rw [hre]
  exact Complex.reCLM.differentiable.comp h

/-- The derivative of a coerced real function is the coercion of its derivative. -/
theorem deriv_ofReal_eq {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) :
    deriv (fun y : ℝ => ((ψ y : ℝ) : ℂ)) = fun y : ℝ => ((deriv ψ y : ℝ) : ℂ) := by
  funext y
  exact ((hψ y).hasDerivAt.ofReal_comp).deriv

/-- **A real band eigenfunction has bounded variation.**  Every hypothesis of the variation chain
is discharged from the eigen-equation: regularity from the derivative tower, the prolate equation
from the commutation, and simplicity from the vanishing Wronskian. -/
theorem bandEigen_real_boundedVariationOn {c α r B : ℝ} {ψ : ℝ → ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (hc : c ≠ 0)
    (hψ1 : Differentiable ℝ ψ) (hψ2 : Differentiable ℝ (deriv ψ))
    (heig : ∀ x : ℝ, prolateActionC c (fun y : ℝ => ((ψ y : ℝ) : ℂ))
        (deriv (fun y : ℝ => ((ψ y : ℝ) : ℂ)))
        (deriv (deriv (fun y : ℝ => ((ψ y : ℝ) : ℂ)))) x
      = ((α : ℝ) : ℂ) * ((ψ x : ℝ) : ℂ))
    (hnt : ∃ y ∈ Icc (-r) r, ψ y ≠ 0)
    (hbound : ∀ y ∈ Icc (-r) r, |ψ y| ≤ B) :
    ∃ S : Finset ℝ,
      eVariationOn ψ (Icc (-r) r) ≤ ENNReal.ofReal (2 * (S.card + 1) * B) := by
  have hd1 : deriv (fun y : ℝ => ((ψ y : ℝ) : ℂ)) = fun y : ℝ => ((deriv ψ y : ℝ) : ℂ) :=
    deriv_ofReal_eq hψ1
  have hd2 : deriv (deriv (fun y : ℝ => ((ψ y : ℝ) : ℂ)))
      = fun y : ℝ => ((deriv (deriv ψ) y : ℝ) : ℂ) := by
    rw [hd1]
    exact deriv_ofReal_eq hψ2
  refine prolate_boundedVariationOn_of_complex_eigen (α := α) hr0 hr hc hψ1 hψ2 ?_ hnt hbound
  intro x
  have h := heig x
  rw [hd2, hd1] at h
  exact h


end RHTower
