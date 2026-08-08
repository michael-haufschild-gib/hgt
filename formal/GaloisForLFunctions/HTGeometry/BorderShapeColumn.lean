import GaloisForLFunctions.HTGeometry.OrbitScaling

/-!
# The class of starting vectors the peel preserves

The peel's induction does not run on a degree profile — dividing the peeled vector by the newest
denominator leaves a *factor* on its leading term, and the shifted operator sees that factor:
`E(f·c) = (δf)·c + f·E(c)`, whose first summand does not drop a degree.  What is preserved is the
exact leading term.  So the induction class is

`u_m − Q_m'/Q_m` has degree at most `−2`,

with the lower entries of degree at most `0`.  On that class the newest column behaves exactly as it
does for the border row: `E(Q_m'/Q_m) = (∏_{i<m}Q_i)·W(Q_m,v_m)/Q_m²` already has degree `−2`, so
every entry below the border does too, and the scaled column's value at infinity is
`(deg Q_m, 0, …, 0)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Q v : ℕ → Polynomial ℂ}

/-! ## The newest column is a scalar orbit -/

/-- **At the newest coordinate the shifted operator is scalar.** -/
theorem gradShift_top (Q v : ℕ → Polynomial ℂ) (m : ℕ) (u : ℕ → CascadeField) :
    gradShift Q v m u m = topShift Q v m (u m) := by
  rw [gradShift, topShift, Finset.sum_range_succ]
  have hlow : ∀ l ∈ Finset.range m, jetResponse Q v m l * u l = 0 := by
    intro l hl
    rw [jetResponse_of_lt Q v (Finset.mem_range.mp hl), zero_mul]
  rw [Finset.sum_eq_zero hlow, zero_add]
  rfl

theorem iterate_gradShift_top (Q v : ℕ → Polynomial ℂ) (m : ℕ) (u : ℕ → CascadeField) (i : ℕ) :
    ((gradShift Q v m)^[i]) u m = ((topShift Q v m)^[i]) (u m) := by
  induction i generalizing u with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, gradShift_top]

/-! ## The border row's own image -/

/-- The shifted operator on the logarithmic derivative is the Wronskian entry. -/
theorem topShift_logFactor_eq (Q v : ℕ → Polynomial ℂ) (n : ℕ) :
    topShift Q v (n + 1) (logFactor (Q (n + 1)) (n + 1))
      = fpderiv (n + 1) (logSum Q v (n + 2)) := by
  have hgrad := gradient_logSum_eq (Q := Q) v (n + 1)
  have hval := congrArg (fun F : ℕ → CascadeField => F (n + 1)) hgrad
  rw [hval, gradShift_top]
  congr 1
  rw [logBorder, if_pos (le_refl (n + 1))]

/-! ## The induction class -/

/-- The starting vectors the peel preserves: the newest entry is the logarithmic derivative up to
degree `−2`. -/
def BorderShape (Q : ℕ → Polynomial ℂ) (m : ℕ) (u : ℕ → CascadeField) : Prop :=
  TopDegLE m (-2) (u m - logFactor (Q m) m)

theorem borderShape_logBorder (Q : ℕ → Polynomial ℂ) (m : ℕ) :
    BorderShape Q m (logBorder Q m) := by
  rw [BorderShape, logBorder, if_pos (le_refl m), sub_self]
  exact topDegLE_zero m (-2)

/-! ## The newest column of a border-shaped vector -/

/-- **The first entry below the border has degree `−2`.** -/
theorem topDegLE_topShift_of_borderShape {n : ℕ} (hQ : Q (n + 1) ≠ 0)
    (hq : 1 ≤ (Q (n + 1)).natDegree) (hv : (v (n + 1)).natDegree = 1)
    {u : ℕ → CascadeField} (hshape : BorderShape Q (n + 1) u)
    (hmem : u (n + 1) - logFactor (Q (n + 1)) (n + 1) ∈ lowSub Q v (n + 1)) :
    TopDegLE (n + 1) (-2) (topShift Q v (n + 1) (u (n + 1))) := by
  have hsplit : u (n + 1)
      = logFactor (Q (n + 1)) (n + 1) + (u (n + 1) - logFactor (Q (n + 1)) (n + 1)) := by
    ring
  rw [hsplit, topShift]
  have hadd : prodDerivation Q v (logFactor (Q (n + 1)) (n + 1)
        + (u (n + 1) - logFactor (Q (n + 1)) (n + 1)))
      + topResponse Q v (n + 1) * (logFactor (Q (n + 1)) (n + 1)
        + (u (n + 1) - logFactor (Q (n + 1)) (n + 1)))
      = topShift Q v (n + 1) (logFactor (Q (n + 1)) (n + 1))
        + topShift Q v (n + 1) (u (n + 1) - logFactor (Q (n + 1)) (n + 1)) := by
    rw [topShift, topShift, map_add]
    ring
  rw [hadd, topShift_logFactor_eq]
  refine TopDegLE.add (topDegLE_fpderiv_logSum_top n hQ hq hv) ?_
  exact topShift_topDegLE (by omega) hmem hshape

/-- **Every entry below the border has degree `−2`.** -/
theorem topDegLE_iterate_of_borderShape {n : ℕ} (hQ : Q (n + 1) ≠ 0)
    (hq : 1 ≤ (Q (n + 1)).natDegree) (hv : (v (n + 1)).natDegree = 1)
    {u : ℕ → CascadeField} (hshape : BorderShape Q (n + 1) u)
    (hmem : u (n + 1) - logFactor (Q (n + 1)) (n + 1) ∈ lowSub Q v (n + 1))
    (hmemu : u (n + 1) ∈ lowSub Q v (n + 1)) (r : ℕ) :
    TopDegLE (n + 1) (-2)
      (((topShift Q v (n + 1))^[r]) (topShift Q v (n + 1) (u (n + 1)))) := by
  have hbase : TopDegLE (n + 1) (-2) (topShift Q v (n + 1) (u (n + 1))) :=
    topDegLE_topShift_of_borderShape hQ hq hv hshape hmem
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      refine topShift_topDegLE (by omega) ?_ ih
      exact iterate_topShift_mem_lowSub (topShift_mem_lowSub hmemu) r

/-- **The border entry of a border-shaped vector has the same residue.** -/
theorem topLim_fx_mul_of_borderShape {n : ℕ} (hq : 1 ≤ (Q (n + 1)).natDegree)
    {u : ℕ → CascadeField} (hshape : BorderShape Q (n + 1) u) :
    TopLim (n + 1) (fx (n + 1) * u (n + 1))
      (algebraMap ℂ CascadeField ((Q (n + 1)).natDegree : ℂ)) := by
  have hsplit : fx (n + 1) * u (n + 1)
      = fx (n + 1) * logFactor (Q (n + 1)) (n + 1)
        + fx (n + 1) * (u (n + 1) - logFactor (Q (n + 1)) (n + 1)) := by
    ring
  rw [hsplit]
  have h1 := topLim_fx_mul_border (Q := Q) n hq
  have h2 : TopLim (n + 1) (fx (n + 1) * (u (n + 1) - logFactor (Q (n + 1)) (n + 1))) 0 := by
    rw [TopLim, sub_zero]
    have h := TopDegLE.mul (topDegLE_fx (n + 1)) hshape
    simpa using h
  have hsum := TopLim.add h1 h2
  rw [add_zero] at hsum
  exact hsum

/-- **The scaled newest column of a border-shaped vector vanishes below the border.** -/
theorem topLim_fx_mul_iterate_of_borderShape {n : ℕ} (hQ : Q (n + 1) ≠ 0)
    (hq : 1 ≤ (Q (n + 1)).natDegree) (hv : (v (n + 1)).natDegree = 1)
    {u : ℕ → CascadeField} (hshape : BorderShape Q (n + 1) u)
    (hmem : u (n + 1) - logFactor (Q (n + 1)) (n + 1) ∈ lowSub Q v (n + 1))
    (hmemu : u (n + 1) ∈ lowSub Q v (n + 1)) (r : ℕ) :
    TopLim (n + 1)
      (fx (n + 1) * (((gradShift Q v (n + 1))^[r + 1]) u (n + 1))) 0 := by
  rw [TopLim, sub_zero, iterate_gradShift_top, Function.iterate_succ_apply]
  have h := TopDegLE.mul (topDegLE_fx (n + 1))
    (topDegLE_iterate_of_borderShape hQ hq hv hshape hmem hmemu r)
  simpa using h

end GaloisForLFunctions.HTGeometry
