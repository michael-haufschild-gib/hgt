import GaloisForLFunctions.RHTower.XiCoordinate

/-!
# The inverse Dunster coordinate

Dunster's exterior weight is written in the phase variable through the inverse coordinate
`X_s(r)`, the exterior point whose phase is `r`.  The coordinate is a strictly increasing continuous
bijection of the exterior ray onto the positive ray, so the inverse exists; what makes it usable is
that it is differentiable with derivative the reciprocal speed.

The image is the whole positive ray because the phase is unbounded: the corpus's lower bracket
`sqrt(1-s) sqrt(x²-1) <= xi_s(x)` already grows without bound.
-/

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The phase exceeds any prescribed level: an explicit exterior point is produced. -/
theorem exists_lt_xiEndpointPhase {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hy : 0 < y) :
    ∃ X, 1 ≤ X ∧ y < xiEndpointPhase s X := by
  refine ⟨Real.sqrt (1 + (2 * y) ^ 2), ?_, ?_⟩
  · exact Real.one_le_sqrt.mpr (by nlinarith)
  · set X : ℝ := Real.sqrt (1 + (2 * y) ^ 2) with hXdef
    have hX1 : (1 : ℝ) ≤ X := by
      rw [hXdef]
      exact Real.one_le_sqrt.mpr (by nlinarith)
    have hXsq : X ^ 2 = 1 + (2 * y) ^ 2 := Real.sq_sqrt (by positivity)
    have hsub : X ^ 2 - 1 = (2 * y) ^ 2 := by rw [hXsq]; ring
    have hsq : Real.sqrt (X ^ 2 - 1) = 2 * y := by
      rw [hsub, Real.sqrt_sq (by positivity)]
    have hlow := (xiEndpointPhase_bounds hs0 (by linarith) hX1).1
    rw [hsq] at hlow
    have hroot : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
    have hhalf : (3 : ℝ) / 5 ≤ Real.sqrt (1 / 2) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sqrt_nonneg (1 / 2 : ℝ)]
    nlinarith [hlow, hroot, hhalf, hy]

/-- **The phase maps the exterior ray onto the positive ray.** -/
theorem image_xiEndpointPhase_Ioi {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    xiEndpointPhase s '' Ioi 1 = Ioi 0 := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_Ioi, ← xiEndpointPhase_one s]
    exact strictMonoOn_xiEndpointPhase hs0 hs1 (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr (le_of_lt hx)) hx
  · intro y hy
    obtain ⟨X, hX1, hXy⟩ := exists_lt_xiEndpointPhase hs0 hs1 hy
    have hmem : y ∈ Ioo 0 (xiEndpointPhase s X) := ⟨hy, hXy⟩
    obtain ⟨x, hx, hxy⟩ := (image_xiEndpointPhase_Ioo hs0 hs1 hX1).symm ▸ hmem
    exact ⟨x, hx.1, hxy⟩

/-- The inverse Dunster coordinate. -/
def xiInverse (s : ℝ) : ℝ → ℝ := Function.invFunOn (xiEndpointPhase s) (Ioi 1)

theorem xiEndpointPhase_xiInverse {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    xiEndpointPhase s (xiInverse s r) = r := by
  have hmem : r ∈ xiEndpointPhase s '' Ioi 1 := by
    rw [image_xiEndpointPhase_Ioi hs0 hs1]
    exact hr
  obtain ⟨x, hx, hxr⟩ := hmem
  exact Function.invFunOn_eq ⟨x, hx, hxr⟩

theorem xiInverse_mem_Ioi {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    xiInverse s r ∈ Ioi 1 := by
  have hmem : r ∈ xiEndpointPhase s '' Ioi 1 := by
    rw [image_xiEndpointPhase_Ioi hs0 hs1]
    exact hr
  obtain ⟨x, hx, hxr⟩ := hmem
  exact Function.invFunOn_mem ⟨x, hx, hxr⟩

theorem xiInverse_xiEndpointPhase {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiInverse s (xiEndpointPhase s x) = x := by
  have hinj : InjOn (xiEndpointPhase s) (Ioi 1) :=
    (injOn_xiEndpointPhase hs0 hs1).mono (fun t ht => le_of_lt (mem_Ioi.mp ht))
  exact hinj.leftInvOn_invFunOn (mem_Ioi.mpr hx)

/-- The inverse coordinate is strictly increasing. -/
theorem strictMonoOn_xiInverse {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    StrictMonoOn (xiInverse s) (Ioi 0) := by
  intro a ha b hb hab
  have hA := xiInverse_mem_Ioi hs0 hs1 ha
  have hB := xiInverse_mem_Ioi hs0 hs1 hb
  have hEa := xiEndpointPhase_xiInverse hs0 hs1 ha
  have hEb := xiEndpointPhase_xiInverse hs0 hs1 hb
  by_contra hcon
  push Not at hcon
  have hmono := strictMonoOn_xiEndpointPhase hs0 hs1
  have hle : xiEndpointPhase s (xiInverse s b) ≤ xiEndpointPhase s (xiInverse s a) :=
    hmono.monotoneOn (mem_Ici.mpr (le_of_lt hB)) (mem_Ici.mpr (le_of_lt hA)) hcon
  rw [hEa, hEb] at hle
  linarith

theorem image_xiInverse_Ioi {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    xiInverse s '' Ioi 0 = Ioi 1 := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact xiInverse_mem_Ioi hs0 hs1 hr
  · intro x hx
    refine ⟨xiEndpointPhase s x, ?_, xiInverse_xiEndpointPhase hs0 hs1 hx⟩
    rw [mem_Ioi, ← xiEndpointPhase_one s]
    exact strictMonoOn_xiEndpointPhase hs0 hs1 (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr (le_of_lt hx)) hx

/-- The inverse coordinate is continuous on the positive ray. -/
theorem continuousAt_xiInverse {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    ContinuousAt (xiInverse s) r := by
  refine (strictMonoOn_xiInverse hs0 hs1).continuousAt_of_image_mem_nhds
    (isOpen_Ioi.mem_nhds hr) ?_
  rw [image_xiInverse_Ioi hs0 hs1]
  exact isOpen_Ioi.mem_nhds (xiInverse_mem_Ioi hs0 hs1 hr)

/-- **The inverse function theorem for the Dunster coordinate.**  The inverse is differentiable with
derivative the reciprocal speed, which is the exact content of `X_s'(r) = 1/xi_s'(X_s(r))`. -/
theorem hasDerivAt_xiInverse {s r : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hr : 0 < r) :
    HasDerivAt (xiInverse s) (xiSpeed s (xiInverse s r))⁻¹ r := by
  have hmem : (1 : ℝ) < xiInverse s r := xiInverse_mem_Ioi hs0 hs1 hr
  refine HasDerivAt.of_local_left_inverse (continuousAt_xiInverse hs0 hs1 hr)
    (hasDerivAt_xiEndpointPhase hs0 hmem) (ne_of_gt (xiSpeed_pos hs1 hmem)) ?_
  filter_upwards [isOpen_Ioi.mem_nhds hr] with y hy
  exact xiEndpointPhase_xiInverse hs0 hs1 hy

end GaloisForLFunctions.RHTower
