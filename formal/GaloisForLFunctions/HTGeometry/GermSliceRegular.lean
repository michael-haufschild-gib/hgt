import GaloisForLFunctions.HTGeometry.DistinguishedGermIndependence

/-!
# The slice homomorphism and regularity

Restricting a germ at the origin of `ℂ^(n+1)` to the first coordinate axis is a ring homomorphism
to the germs at the origin of `ℂ`.  A germ is *regular* in the distinguished coordinate exactly when
its slice is nonzero, so regularity is multiplicative: a product is regular if and only if both
factors are.  That is what lets one linear change of coordinates make finitely many germs regular at
once — apply it to their product.

A distinguished polynomial has slice `z^d`, hence is regular as soon as it is nonconstant.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

theorem cons_zero_zero : (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp

theorem analyticAt_consZero :
    AnalyticAt ℂ (fun z : ℂ => (Fin.cons z (0 : Fin n → ℂ) : Fin (n + 1) → ℂ)) 0 := by
  have hlin : AnalyticAt ℂ
      (fun z : ℂ => z • (Fin.cons (1 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ)) 0 :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (Fin.cons (1 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ)).analyticAt 0
  have hfun : (fun z : ℂ => z • (Fin.cons (1 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ))
      = fun z : ℂ => (Fin.cons z (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) := by
    funext z
    exact (cons_zero_eq_smul z).symm
  rwa [hfun] at hlin

/-- Restriction of a germ to the first coordinate axis. -/
noncomputable def germSlice (n : ℕ) :
    AnalyticGerm (0 : Fin (n + 1) → ℂ) →+* AnalyticGerm (0 : ℂ) :=
  analyticGermPullback analyticAt_consZero cons_zero_zero

theorem germSlice_analyticGermOf {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) :
    (germSlice n (analyticGermOf hf) : Germ (𝓝 (0 : ℂ)) ℂ)
      = ((f ∘ fun z : ℂ => (Fin.cons z (0 : Fin n → ℂ) : Fin (n + 1) → ℂ)) : ℂ → ℂ) :=
  analyticGermPullback_analyticGermOf analyticAt_consZero cons_zero_zero hf

/-- **A germ is regular in the distinguished coordinate exactly when its slice is nonzero.** -/
theorem germSlice_ne_zero_iff {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) :
    germSlice n (analyticGermOf hf) ≠ 0
      ↔ ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
  constructor
  · intro h hc
    refine h (Subtype.ext ?_)
    rw [germSlice_analyticGermOf hf, ZeroMemClass.coe_zero]
    exact Germ.coe_eq.mpr hc
  · intro h hc
    refine h ?_
    have := congrArg (fun x : AnalyticGerm (0 : ℂ) => (x : Germ (𝓝 (0 : ℂ)) ℂ)) hc
    rw [germSlice_analyticGermOf hf, ZeroMemClass.coe_zero] at this
    exact Germ.coe_eq.mp this

/-- **Regularity is multiplicative.**  If a product of germs is regular, so is each factor. -/
theorem germSlice_ne_zero_of_mul_ne_zero {x y : AnalyticGerm (0 : Fin (n + 1) → ℂ)}
    (h : germSlice n (x * y) ≠ 0) : germSlice n x ≠ 0 ∧ germSlice n y ≠ 0 := by
  rw [map_mul] at h
  constructor
  · intro hx
    exact h (by rw [hx, zero_mul])
  · intro hy
    exact h (by rw [hy, mul_zero])

theorem germSlice_mul_ne_zero {x y : AnalyticGerm (0 : Fin (n + 1) → ℂ)}
    (hx : germSlice n x ≠ 0) (hy : germSlice n y ≠ 0) : germSlice n (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

/-! ## The slice of a distinguished polynomial -/

theorem tail_zero : (Fin.tail (0 : Fin (n + 1) → ℂ) : Fin n → ℂ) = 0 := by
  funext i
  simp [Fin.tail]

/-- **A distinguished polynomial of positive degree has a regular germ.** -/
theorem germSlice_germEval_distPoly_ne_zero {d : ℕ} (hd : 0 < d)
    {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → analyticGermValue (0 : Fin n → ℂ) (α j) = 0) :
    germSlice n (germEval n (distPoly d α)) ≠ 0 := by
  classical
  choose a haA haeq using fun j : ℕ => (α j).2
  have hαeq : ∀ j, α j = analyticGermOf (haA j) := fun j => Subtype.ext (haeq j).symm
  have hazero : ∀ j, j < d → a j (0 : Fin n → ℂ) = 0 := by
    intro j hj
    have := hzero j hj
    rw [hαeq j, analyticGermValue_of (haA j)] at this
    exact this
  have haAtail : ∀ j, AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ => a j (Fin.tail w))
      (0 : Fin (n + 1) → ℂ) := by
    intro j
    have hg' : AnalyticAt ℂ (a j) (Fin.tail (0 : Fin (n + 1) → ℂ)) := by
      rw [tail_zero]
      exact haA j
    exact hg'.comp analyticAt_tail
  have hF : AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ =>
      (w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j)
      (0 : Fin (n + 1) → ℂ) := by
    refine (analyticAt_coordZero.pow d).add ?_
    refine Finset.analyticAt_sum _ fun j _ => ?_
    exact (haAtail j).mul (analyticAt_coordZero.pow j)
  have hgerm : germEval n (distPoly d α) = analyticGermOf hF := by
    refine Subtype.ext ?_
    rw [germEval_distPoly]
    simp only [hαeq]
    rw [coe_germDistinguished haA, analyticGermOf_val]
  rw [hgerm]
  refine (germSlice_ne_zero_iff hF).mpr ?_
  intro hc
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp hc
  have hz : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hval := hεspec (show dist ((ε / 2 : ℝ) : ℂ) 0 < ε by
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  simp only [Pi.zero_apply, Fin.cons_zero, Fin.tail_cons] at hval
  have hsum : ∑ j ∈ Finset.range d, a j (0 : Fin n → ℂ) * ((ε / 2 : ℝ) : ℂ) ^ j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hazero j (Finset.mem_range.mp hj), zero_mul]
  rw [hsum, add_zero] at hval
  exact pow_ne_zero d hz hval

end GaloisForLFunctions.HTGeometry
