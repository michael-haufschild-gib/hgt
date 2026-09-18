import GaloisForLFunctions.RHTower.EisensteinTruncatedPairingHolomorphic

/-!
# The Maass–Selberg relation on the quarter-plane, and the diagonal

Both sides of the cleared relation `(u−v)(u+v) ∫_𝒟 Λ^Y E_u · Λ^Y E_v = R(u, v, Y)` are holomorphic
in `u ∈ Ω` (for fixed `v ∈ Ω`) and in `v ∈ Ω` (for fixed `u ∈ Ω`); the relation holds on the open
region `Re u > Re v > ½` (`maassSelberg_region`), hence, by the identity theorem in `u` and then in
`v`, on all of `Ω × Ω`.  Letting `v → u` gives the diagonal value
`∫_𝒟 (Λ^Y E_u)² = −msDiag u Y / (2u)`, and on the line `u = it` the explicit `msLineValue t Y`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The truncated pairing `P_Y(u, v) = ∫_𝒟 Λ^Y E_u · Λ^Y E_v dμ`. -/
def truncatedPairing (Y : ℝ) (u v : ℂ) : ℂ :=
  ∫ z in fd, truncatedLineModel u Y z * truncatedLineModel v Y z

/-! ## Holomorphy of the right-hand side -/

theorem differentiableOn_msA : DifferentiableOn ℂ msA eisensteinLineDomain :=
  fun _ hu => (hasDerivAt_msA hu).differentiableAt.differentiableWithinAt

theorem differentiableOn_msB : DifferentiableOn ℂ msB eisensteinLineDomain :=
  fun _ hu => (hasDerivAt_msB hu).differentiableAt.differentiableWithinAt

theorem differentiableOn_msRight_left (v : ℂ) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (fun u => msRight u v Y) eisensteinLineDomain := by
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  unfold msRight
  have h1 : DifferentiableOn ℂ (fun u : ℂ => (Y : ℂ) ^ (u + v)) eisensteinLineDomain :=
    (differentiableOn_id.add_const v).const_cpow (Or.inl hYne)
  have h2 : DifferentiableOn ℂ (fun u : ℂ => (Y : ℂ) ^ (u - v)) eisensteinLineDomain :=
    (differentiableOn_id.sub_const v).const_cpow (Or.inl hYne)
  have h3 : DifferentiableOn ℂ (fun u : ℂ => (Y : ℂ) ^ (v - u)) eisensteinLineDomain :=
    (differentiableOn_id.const_sub v).const_cpow (Or.inl hYne)
  have h4 : DifferentiableOn ℂ (fun u : ℂ => (Y : ℂ) ^ (-u - v)) eisensteinLineDomain :=
    (differentiableOn_id.neg.sub_const v).const_cpow (Or.inl hYne)
  have hA := differentiableOn_msA
  have hB := differentiableOn_msB
  have hsub : DifferentiableOn ℂ (fun u : ℂ => u - v) eisensteinLineDomain :=
    differentiableOn_id.sub_const v
  have hadd : DifferentiableOn ℂ (fun u : ℂ => u + v) eisensteinLineDomain :=
    differentiableOn_id.add_const v
  exact ((hsub.mul (hA.mul_const _)).mul h1).add
    (hadd.mul (((hA.mul_const _).mul h2).sub ((hB.mul_const _).mul h3))) |>.sub
    ((hsub.mul (hB.mul_const _)).mul h4)

theorem differentiableOn_msRight_right (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (fun v => msRight u v Y) eisensteinLineDomain := by
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  unfold msRight
  have h1 : DifferentiableOn ℂ (fun v : ℂ => (Y : ℂ) ^ (u + v)) eisensteinLineDomain :=
    (differentiableOn_id.const_add u).const_cpow (Or.inl hYne)
  have h2 : DifferentiableOn ℂ (fun v : ℂ => (Y : ℂ) ^ (u - v)) eisensteinLineDomain :=
    (differentiableOn_id.const_sub u).const_cpow (Or.inl hYne)
  have h3 : DifferentiableOn ℂ (fun v : ℂ => (Y : ℂ) ^ (v - u)) eisensteinLineDomain :=
    (differentiableOn_id.sub_const u).const_cpow (Or.inl hYne)
  have h4 : DifferentiableOn ℂ (fun v : ℂ => (Y : ℂ) ^ (-u - v)) eisensteinLineDomain :=
    (differentiableOn_id.const_sub (-u)).const_cpow (Or.inl hYne)
  have hA := differentiableOn_msA
  have hB := differentiableOn_msB
  have hsub : DifferentiableOn ℂ (fun v : ℂ => u - v) eisensteinLineDomain :=
    differentiableOn_id.const_sub u
  have hadd : DifferentiableOn ℂ (fun v : ℂ => u + v) eisensteinLineDomain :=
    differentiableOn_id.const_add u
  exact ((hsub.mul (hA.const_mul _)).mul h1).add
    (hadd.mul (((hB.const_mul _).mul h2).sub ((hA.const_mul _).mul h3))) |>.sub
    ((hsub.mul (hB.const_mul _)).mul h4)

/-! ## The identity theorem -/

/-- The cleared defect `G(u, v) = (u−v)(u+v) P_Y(u,v) − R(u,v,Y)`. -/
def clearedDefect (Y : ℝ) (u v : ℂ) : ℂ :=
  (u - v) * (u + v) * truncatedPairing Y u v - msRight u v Y

theorem analyticOnNhd_clearedDefect_left (v : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    AnalyticOnNhd ℂ (fun u => clearedDefect Y u v) eisensteinLineDomain := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_eisensteinLineDomain
  unfold clearedDefect truncatedPairing
  exact (((differentiableOn_id.sub_const v).mul (differentiableOn_id.add_const v)).mul
    (differentiableOn_truncatedPairing_left v hY)).sub (differentiableOn_msRight_left v (by linarith))

theorem analyticOnNhd_clearedDefect_right (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    AnalyticOnNhd ℂ (fun v => clearedDefect Y u v) eisensteinLineDomain := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_eisensteinLineDomain
  unfold clearedDefect truncatedPairing
  exact (((differentiableOn_id.const_sub u).mul (differentiableOn_id.const_add u)).mul
    (differentiableOn_truncatedPairing_right u hY)).sub (differentiableOn_msRight_right u (by linarith))

/-- Step A: continuation in `u` for `Re v > ½`. -/
theorem clearedDefect_eq_zero_of_re {v : ℂ} (hv1 : 1 / 2 < v.re) (hv : v ∈ eisensteinLineDomain)
    {Y : ℝ} (hY : 1 ≤ Y) {u : ℂ} (hu : u ∈ eisensteinLineDomain) : clearedDefect Y u v = 0 := by
  have hU : IsOpen {u : ℂ | u ∈ eisensteinLineDomain ∧ v.re < u.re} :=
    isOpen_eisensteinLineDomain.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hz₀ : v + 1 ∈ {u : ℂ | u ∈ eisensteinLineDomain ∧ v.re < u.re} := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp; linarith [hv.1]
    · simp; exact hv.2
    · simp
  have heq : (fun u => clearedDefect Y u v) =ᶠ[𝓝 (v + 1)] fun _ => 0 := by
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds hz₀) fun u hu' => ?_
    unfold clearedDefect truncatedPairing
    rw [maassSelberg_region hv1 hu'.2 hv hY, sub_self]
  exact (analyticOnNhd_clearedDefect_left v hY).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const isPreconnected_eisensteinLineDomain hz₀.1 heq hu

/-- **The Maass–Selberg relation on `Ω × Ω`.** -/
theorem maassSelberg_lineModel {u v : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    (u - v) * (u + v) * truncatedPairing Y u v = msRight u v Y := by
  have hV : IsOpen {v : ℂ | v ∈ eisensteinLineDomain ∧ 1 / 2 < v.re} :=
    isOpen_eisensteinLineDomain.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hz₀ : (1 + Complex.I : ℂ) ∈ {v : ℂ | v ∈ eisensteinLineDomain ∧ 1 / 2 < v.re} := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> norm_num
  have heq : (fun v => clearedDefect Y u v) =ᶠ[𝓝 (1 + Complex.I)] fun _ => 0 := by
    refine Filter.eventuallyEq_of_mem (hV.mem_nhds hz₀) fun v hv' => ?_
    exact clearedDefect_eq_zero_of_re hv'.2 hv'.1 hY hu
  have h := (analyticOnNhd_clearedDefect_right u hY).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const isPreconnected_eisensteinLineDomain hz₀.1 heq hv
  unfold clearedDefect at h
  exact sub_eq_zero.mp h

/-! ## The diagonal -/

/-- **The diagonal value** `∫_𝒟 (Λ^Y E_u)² = −msDiag u Y / (2u)` for `u ∈ Ω`. -/
theorem truncatedPairing_diag {u : ℂ} (hu : u ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    truncatedPairing Y u u = -msDiag u Y / (2 * u) := by
  refine eq_neg_msDiag_div_of_cleared (P := fun v => truncatedPairing Y u v) hu (by linarith) ?_ ?_
  · exact ((differentiableOn_truncatedPairing_right u hY).differentiableAt
      (isOpen_eisensteinLineDomain.mem_nhds hu)).continuousAt
  · refine eventually_nhdsWithin_of_eventually_nhds ?_
    filter_upwards [isOpen_eisensteinLineDomain.mem_nhds hu] with v hv
    exact maassSelberg_lineModel hu hv hY

/-- **The diagonal on the critical line.** -/
theorem truncatedPairing_line {t : ℝ} (ht : 0 < t) {Y : ℝ} (hY : 1 ≤ Y) :
    truncatedPairing Y ((t : ℂ) * Complex.I) ((t : ℂ) * Complex.I) = msLineValue t Y := by
  rw [truncatedPairing_diag (I_mul_mem_eisensteinLineDomain ht) hY, neg_msDiag_div_line ht]

end

end RHTower
