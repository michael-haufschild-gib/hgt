import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.Products
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Sharp geodesic chord addition for unequal unitary approximations -/
open Real Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AngularError
noncomputable section

private abbrev Mat (I : Type*) := Matrix I I ℂ
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem arccos_le_of_cos_le {c t : ℝ} (hc1 : -1 ≤ c) (hc2 : c ≤ 1)
    (ht0 : 0 ≤ t) (htpi : t ≤ π) (h : cos t ≤ c) : arccos c ≤ t := by
  by_contra! hlt
  have hanti := strictAntiOn_cos ⟨ht0, htpi⟩ ⟨arccos_nonneg c, arccos_le_pi c⟩ hlt
  rw [cos_arccos hc1 hc2] at hanti
  exact hanti.not_ge h

private theorem unit_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v w : E} {α : ℝ} (hα0 : 0 ≤ α) (hαpi : 2 * α ≤ π)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hd : ‖v - w‖ ≤ 2 * sin α) :
    -1 ≤ inner ℝ v w ∧ inner ℝ v w ≤ 1 ∧
      0 ≤ arccos (inner ℝ v w) ∧ arccos (inner ℝ v w) ≤ 2 * α ∧
      inner ℝ (v - (inner ℝ v w) • w) w = 0 ∧
      ‖v - (inner ℝ v w) • w‖ = sin (arccos (inner ℝ v w)) := by
  let c := inner ℝ v w
  let θ := arccos c
  have habs : |c| ≤ 1 := by
    simpa only [c, hv, hw, mul_one] using abs_real_inner_le_norm v w
  obtain ⟨hc1, hc2⟩ := abs_le.mp habs
  have hdsq : ‖v - w‖ ^ 2 ≤ (2 * sin α) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [norm_sub_sq_real, hv, hw] at hdsq
  have hcos2 : cos (2 * α) ≤ c := by
    have h1 := cos_two_mul' α
    have h2 := sin_sq_add_cos_sq α
    change cos (2 * α) ≤ inner ℝ v w
    nlinarith only [hdsq, h1, h2]
  have hθ0 : 0 ≤ θ := arccos_nonneg c
  have hθle : θ ≤ 2 * α := arccos_le_of_cos_le hc1 hc2 (by positivity) hαpi hcos2
  have horth : inner ℝ (v - c • w) w = 0 := by
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hw]
    simp [c]
  have hnorm_sq : ‖v - c • w‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv, hw,
      inner_smul_right]
    change 1 ^ 2 - 2 * (c * c) + c ^ 2 * 1 ^ 2 = 1 - c ^ 2
    ring
  have hnorm : ‖v - c • w‖ = sin θ := by
    rw [sin_arccos c, ← hnorm_sq, sqrt_sq (norm_nonneg _)]
  exact ⟨hc1, hc2, hθ0, hθle, horth, hnorm⟩

/-- Two equal-length vectors at chord errors 2 sin α and 2 sin β from a common
reference vector lie within chord error 2 sin(α + β) whenever α + β ≤ π/2. -/
theorem common_geodesic_chord {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y z : E} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ π / 2)
    (hx : ‖x‖ = ‖y‖) (hz : ‖z‖ = ‖y‖)
    (hxy : ‖x - y‖ ≤ 2 * sin α * ‖y‖) (hzy : ‖z - y‖ ≤ 2 * sin β * ‖y‖) :
    ‖x - z‖ ≤ 2 * sin (α + β) * ‖y‖ := by
  by_cases h0 : ‖y‖ = 0
  · simp only [norm_eq_zero.mp (hx.trans h0), norm_eq_zero.mp (hz.trans h0), h0,
      sub_self, norm_zero, mul_zero, le_refl]
  have hR : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm h0)
  let a := ‖y‖⁻¹ • x
  let w := ‖y‖⁻¹ • y
  let b := ‖y‖⁻¹ • z
  have unit_len (v : E) (hv : ‖v‖ = ‖y‖) : ‖‖y‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hv, inv_mul_cancel₀ hR.ne']
  have ha : ‖a‖ = 1 := unit_len x hx
  have hw : ‖w‖ = 1 := unit_len y rfl
  have hb : ‖b‖ = 1 := unit_len z hz
  have haw : ‖a - w‖ ≤ 2 * sin α := by
    change ‖‖y‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa only [mul_comm ‖y‖] using hxy)
  have hbw : ‖b - w‖ ≤ 2 * sin β := by
    change ‖‖y‖⁻¹ • z - ‖y‖⁻¹ • y‖ ≤ _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa only [mul_comm ‖y‖] using hzy)
  obtain ⟨hc1, hc1', hθ1, hθ1le, horth1, hu1⟩ :=
    unit_decomp hα (by linarith only [hβ, hsum]) ha hw haw
  obtain ⟨hc2, hc2', hθ2, hθ2le, horth2, hu2⟩ :=
    unit_decomp hβ (by linarith only [hα, hsum]) hb hw hbw
  let c₁ := inner ℝ a w
  let c₂ := inner ℝ b w
  let θ₁ := arccos c₁
  let θ₂ := arccos c₂
  let u₁ := a - c₁ • w
  let u₂ := b - c₂ • w
  have hsplit : a - b = (c₁ - c₂) • w + (u₁ - u₂) := by
    dsimp only [u₁, u₂]
    rw [sub_sub_sub_comm, ← sub_smul]
    abel
  have horth : inner ℝ ((c₁ - c₂) • w) (u₁ - u₂) = 0 := by
    rw [inner_smul_left, inner_sub_right, real_inner_comm u₁ w, real_inner_comm u₂ w]
    dsimp only [u₁, u₂, c₁, c₂]
    rw [horth1, horth2]
    simp
  have hu_le : ‖u₁ - u₂‖ ≤ sin θ₁ + sin θ₂ :=
    (norm_sub_le u₁ u₂).trans_eq (by rw [hu1, hu2])
  have hsin_nonneg : 0 ≤ sin θ₁ + sin θ₂ := by
    rw [← hu1, ← hu2]; positivity
  have hu_sq : ‖u₁ - u₂‖ ^ 2 ≤ (sin θ₁ + sin θ₂) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu_le 2
  have hab_sq : ‖a - b‖ ^ 2 ≤ 2 - 2 * cos (θ₁ + θ₂) := by
    rw [hsplit, norm_add_sq_real, horth, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hw]
    have hca1 : c₁ = cos θ₁ := (cos_arccos hc1 hc1').symm
    have hca2 : c₂ = cos θ₂ := (cos_arccos hc2 hc2').symm
    rw [hca1, hca2, cos_add]
    have hs1 := sin_sq_add_cos_sq θ₁
    have hs2 := sin_sq_add_cos_sq θ₂
    nlinarith only [hu_sq, hs1, hs2]
  have hcos_mono : cos (2 * (α + β)) ≤ cos (θ₁ + θ₂) :=
    strictAntiOn_cos.antitoneOn ⟨by positivity, by linarith only [hθ1le, hθ2le, hsum]⟩
      ⟨by positivity, by linarith only [hsum]⟩ (by linarith only [hθ1le, hθ2le])
  have hsin_sum : 0 ≤ sin (α + β) :=
    sin_nonneg_of_nonneg_of_le_pi (add_nonneg hα hβ) (by linarith only [hsum, pi_pos])
  have hab_le : ‖a - b‖ ≤ 2 * sin (α + β) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have h1 := cos_two_mul' (α + β)
    have h2 := sin_sq_add_cos_sq (α + β)
    nlinarith only [hab_sq, hcos_mono, h1, h2]
  have hback : x - z = ‖y‖ • (a - b) := by
    dsimp only [a, b]
    rw [← smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [hback, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_comm ‖y‖]
  exact mul_le_mul_of_nonneg_right hab_le hR.le

/-- Operator-norm geodesic chord addition on the unitary group. -/
theorem common_unitary_geodesic_chord {I : Type*} [Fintype I] [DecidableEq I]
    {X Y Z : Mat I} (hX : X ∈ unitary (Mat I)) (hY : Y ∈ unitary (Mat I))
    (hZ : Z ∈ unitary (Mat I)) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ π / 2)
    (hx : ‖X - Y‖ ≤ 2 * sin α) (hz : ‖Z - Y‖ ≤ 2 * sin β) :
    ‖X - Z‖ ≤ 2 * sin (α + β) := by
  let L := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
  have norm_image (U : Mat I) (hU : U ∈ unitary (Mat I)) (v : EuclideanSpace ℂ I) :
      ‖L U v‖ = ‖v‖ := by
    apply RHTower.deningerUnitary_norm_apply
    have h := congrArg L (Unitary.mem_iff.mp hU).1
    simpa only [map_mul, map_one, map_star, ContinuousLinearMap.star_eq_adjoint] using h
  have dist_image (U : Mat I) {r : ℝ} (he : ‖U - Y‖ ≤ r) (v : EuclideanSpace ℂ I) :
      ‖L U v - L Y v‖ ≤ r * ‖v‖ := by
    have h := (L (U - Y)).le_opNorm v
    rw [map_sub, _root_.sub_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by rwa [← map_sub]) (norm_nonneg _))
  have hs := sin_nonneg_of_nonneg_of_le_pi (add_nonneg hα hβ) (by linarith only [hsum, pi_pos])
  change ‖L (X - Z)‖ ≤ _
  rw [map_sub]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg two_pos.le hs)
  intro v
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ I) := InnerProductSpace.complexToReal
  have h := common_geodesic_chord (x := L X v) (y := L Y v) (z := L Z v) hα hβ hsum
    ((norm_image X hX v).trans (norm_image Y hY v).symm)
    ((norm_image Z hZ v).trans (norm_image Y hY v).symm)
    (by rw [norm_image Y hY]; exact dist_image X hx v)
    (by rw [norm_image Y hY]; exact dist_image Z hz v)
  simpa only [_root_.sub_apply, norm_image Y hY] using h

private theorem unitary_smul {I : Type*} [Fintype I] [DecidableEq I] {U : Matrix I I ℂ}
    (hU : U ∈ unitary (Matrix I I ℂ)) {z : ℂ} (hz : ‖z‖ = 1) :
    z • U ∈ unitary (Matrix I I ℂ) := by
  have hc : star z * z = 1 := by rw [Complex.star_def, Complex.conj_mul', hz]; norm_num
  have hc' : z * star z = 1 := (mul_comm ..).trans hc
  obtain ⟨hl, hr⟩ := Unitary.mem_iff.mp hU
  apply Unitary.mem_iff.mpr
  simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, hc', hl, hr, one_smul, and_self]

/-- Multiplying two physical approximations adds their gate budgets and their
half-chord angles up to π/2. -/
theorem affordable_add_geodesic {N i j : ℕ} (H : selfAdjoint (Reg N)) {x y α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsum : α + β ≤ π / 2)
    (hx : HasProjectiveCircuitApproximation N (2 * sin α) i (unitaryEvolution H.val x))
    (hy : HasProjectiveCircuitApproximation N (2 * sin β) j (unitaryEvolution H.val y)) :
    HasProjectiveCircuitApproximation N (2 * sin (α + β)) (i + j) (unitaryEvolution H.val (x + y)) := by
  obtain ⟨c, hc, C, hC, hx'⟩ := hx
  obtain ⟨d, hd, D, hD, hy'⟩ := hy
  let U := unitaryEvolution H.val x
  let V := unitaryEvolution H.val y
  let A : Reg N := c • (C.eval : Reg N)
  let B : Reg N := d • (D.eval : Reg N)
  have hU := unitaryEvolution_mem_unitary H.2 x
  have hV := unitaryEvolution_mem_unitary H.2 y
  have hA : A ∈ unitary (Reg N) := unitary_smul C.eval.property hc
  have hB : B ∈ unitary (Reg N) := unitary_smul D.eval.property hd
  have hVn : ‖V‖ = 1 := CStarRing.norm_coe_unitary ⟨V, hV⟩
  have hAn : ‖A‖ = 1 := CStarRing.norm_coe_unitary ⟨A, hA⟩
  have h₁ : ‖U * V - A * V‖ ≤ 2 * sin α := by
    rw [← sub_mul]
    exact (Matrix.l2_opNorm_mul _ _).trans (by rw [hVn, mul_one]; exact hx')
  have h₂ : ‖A * B - A * V‖ ≤ 2 * sin β := by
    rw [← mul_sub]
    exact (Matrix.l2_opNorm_mul _ _).trans (by rw [hAn, one_mul, norm_sub_rev B V]; exact hy')
  have hh := common_unitary_geodesic_chord ((unitary _).mul_mem hU hV) ((unitary _).mul_mem hA hV)
    ((unitary _).mul_mem hA hB) hα hβ hsum h₁ h₂
  have hprod : U * V = unitaryEvolution H.val (x + y) := by
    simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul H (x + y) y
  have hword : A * B = (c * d) • ((C.mul D).eval : Reg N) := by
    rw [TwoQubitCircuit.mul_eval]
    change (c • (C.eval : Reg N)) * (d • (D.eval : Reg N)) = _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rfl
  refine ⟨c * d, by rw [norm_mul, hc, hd, mul_one], C.mul D, ?_, ?_⟩
  · rw [TwoQubitCircuit.mul_gateCount]; omega
  · rwa [hprod, hword] at hh

#print axioms common_geodesic_chord
#print axioms common_unitary_geodesic_chord
#print axioms affordable_add_geodesic
end
end GaloisForLFunctions.HTGeometry.AngularError
