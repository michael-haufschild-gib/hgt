import GaloisForLFunctions.HTGeometry.Probability.ComplexSphereMellin
import GaloisForLFunctions.HTGeometry.GammaNatShift

/-!
# Angular concentration of complex monomials

On the unit sphere in complex dimension `n + 1`, the coordinate Mellin transform is a
reciprocal polynomial. Its leading term gives exact asymptotic constants for every positive
real `Lᵖ` exponent. Comparing two exponents quantifies concentration near the coordinate circle.
-/

open MeasureTheory Set Metric Filter Topology
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The normalized coordinate Mellin moment on the sphere in complex dimension `n + 1`. -/
def complexSphereMellin (n : ℕ) (s : ℝ) : ℝ :=
  complexBlockSphereMellin (EuclideanSpace ℝ (Fin (2 * n))) s

/-- The coordinate moment in complex dimension `n + 1` is a Gamma quotient. -/
theorem complexSphereMellin_eq_gamma (n : ℕ) {s : ℝ} (hs : -1 < s) :
    complexSphereMellin n s =
      Real.Gamma (s + 1) * (n.factorial : ℝ) / Real.Gamma (s + 1 + n) := by
  rw [complexSphereMellin, complexBlockSphereMellin_eq _ hs]
  have hd : Module.finrank ℝ (BlockSpace ℂ (EuclideanSpace ℝ (Fin (2 * n)))) =
      2 + 2 * n := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × EuclideanSpace ℝ (Fin (2 * n)))).finrank_eq,
      Module.finrank_prod, Complex.finrank_real_complex]
    simp
  rw [hd]
  have he : ((2 + 2 * n : ℕ) : ℝ) / 2 = (n : ℝ) + 1 := by push_cast; ring
  rw [he, Real.Gamma_nat_eq_factorial]
  congr 2
  ring

/-- The exact coordinate Mellin transform is a reciprocal polynomial of degree `n`. -/
theorem complexSphereMellin_eq_prod (n : ℕ) {s : ℝ} (hs : -1 < s) :
    complexSphereMellin n s =
      (n.factorial : ℝ) / ∏ j ∈ Finset.range n, (s + 1 + j) := by
  rw [complexSphereMellin_eq_gamma n hs,
    _root_.HTGeometry.Real.Gamma_add_nat (s + 1) n (by
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith only [hs, hj])]
  have hG := (Real.Gamma_pos_of_pos (by linarith only [hs] : 0 < s + 1)).ne'
  rw [mul_comm (Real.Gamma (s + 1)), mul_div_mul_right _ _ hG]

/-- Coordinate moments have leading term `n! / sⁿ`. -/
theorem tendsto_complexSphereMellin_scaled (n : ℕ) :
    Tendsto (fun s : ℝ => s ^ n * complexSphereMellin n s) atTop
      (𝓝 (n.factorial : ℝ)) := by
  have hprod : Tendsto (fun s : ℝ => ∏ j ∈ Finset.range n, (1 + (1 + (j : ℝ)) / s))
      atTop (𝓝 1) := by
    have hfactor (j : ℕ) : Tendsto (fun s : ℝ => 1 + (1 + (j : ℝ)) / s)
        atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add
        (Filter.Tendsto.div_atTop (f := fun _ : ℝ => 1 + (j : ℝ))
          tendsto_const_nhds tendsto_id)
    simpa using tendsto_finset_prod (Finset.range n) (fun j _ => hfactor j)
  have he : ∀ᶠ s : ℝ in atTop,
      s ^ n * complexSphereMellin n s =
        (n.factorial : ℝ) / ∏ j ∈ Finset.range n, (1 + (1 + (j : ℝ)) / s) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [complexSphereMellin_eq_prod n (by linarith only [hs])]
    have hfactor (j : ℕ) : 1 + (1 + (j : ℝ)) / s = (s + 1 + j) / s := by
      field_simp
      ring
    simp_rw [hfactor]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    have hden : (∏ j ∈ Finset.range n, (s + 1 + (j : ℝ))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith only [hs, hj]
    field_simp
  apply Filter.Tendsto.congr' he.symm
  simpa using tendsto_const_nhds.div hprod one_ne_zero

/-- The normalized `Lᵖ` size of a coordinate monomial, extended to real degree. -/
def complexSphereMonomialNorm (n : ℕ) (p m : ℝ) : ℝ :=
  complexSphereMellin n (m * p / 2) ^ (1 / p)

/-- At natural degree, the definition is the integral formula for the normalized `Lᵖ` norm. -/
theorem complexSphereMonomialNorm_nat_eq (n m : ℕ) (p : ℝ) :
    complexSphereMonomialNorm n p m =
      ((∫ ω : sphere (0 : BlockSpace ℂ (EuclideanSpace ℝ (Fin (2 * n)))) 1,
        ‖(ω.1 : BlockSpace ℂ (EuclideanSpace ℝ (Fin (2 * n)))).fst ^ m‖ ^ p
          ∂volume.toSphere) /
        (volume.toSphere : Measure
          (sphere (0 : BlockSpace ℂ (EuclideanSpace ℝ (Fin (2 * n)))) 1)).real univ) ^
            (1 / p) := by
  unfold complexSphereMonomialNorm complexSphereMellin complexBlockSphereMellin
  congr 2
  apply integral_congr_ae
  filter_upwards with ω
  rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

/-- The positive constant in the asymptotic formula for coordinate monomial norms. -/
def complexSphereMonomialConstant (n : ℕ) (p : ℝ) : ℝ :=
  ((n.factorial : ℝ) * (2 / p) ^ n) ^ (1 / p)

theorem complexSphereMonomialConstant_pos (n : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < complexSphereMonomialConstant n p := by
  apply Real.rpow_pos_of_pos
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (pow_pos (div_pos two_pos hp) n)

/-- A coordinate monomial has positive normalized size at every nonnegative degree. -/
theorem complexSphereMonomialNorm_pos (n : ℕ) {p m : ℝ} (hp : 0 < p) (hm : 0 ≤ m) :
    0 < complexSphereMonomialNorm n p m := by
  apply Real.rpow_pos_of_pos
  apply complexBlockSphereMellin_pos
  have hmp : 0 ≤ m * p / 2 := div_nonneg (mul_nonneg hm hp.le) (by norm_num)
  linarith only [hmp]

/-- In complex dimension one, every coordinate power has normalized size one. -/
theorem complexSphereMonomialNorm_zero {p m : ℝ} (hp : 0 < p) (hm : 0 ≤ m) :
    complexSphereMonomialNorm 0 p m = 1 := by
  have hs : -1 < m * p / 2 := by
    have hmp : 0 ≤ m * p / 2 := div_nonneg (mul_nonneg hm hp.le) (by norm_num)
    linarith only [hmp]
  simp only [complexSphereMonomialNorm, complexSphereMellin_eq_prod 0 hs,
    Nat.factorial_zero, Nat.cast_one, Finset.range_zero, Finset.prod_empty, div_one,
    Real.one_rpow]

/-- Exact asymptotic constant for the `Lᵖ` size of high coordinate powers. -/
theorem tendsto_complexSphereMonomialNorm_scaled (n : ℕ) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun m : ℝ => m ^ ((n : ℝ) / p) * complexSphereMonomialNorm n p m)
      atTop (𝓝 (complexSphereMonomialConstant n p)) := by
  have harg : Tendsto (fun m : ℝ => m * p / 2) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_assoc] using
      (tendsto_id.atTop_mul_const (div_pos hp two_pos))
  have hscaled : Tendsto
      (fun m : ℝ => m ^ n * complexSphereMellin n (m * p / 2)) atTop
        (𝓝 ((n.factorial : ℝ) * (2 / p) ^ n)) := by
    have h := ((tendsto_complexSphereMellin_scaled n).comp harg).const_mul ((2 / p) ^ n)
    have he (m : ℝ) :
        (2 / p) ^ n * ((m * p / 2) ^ n * complexSphereMellin n (m * p / 2)) =
          m ^ n * complexSphereMellin n (m * p / 2) := by
      rw [← mul_assoc, ← mul_pow]
      have hc : (2 / p) * (m * p / 2) = m := by field_simp
      rw [hc]
    simpa only [Function.comp_apply, he, mul_comm ((2 / p) ^ n)] using h
  have hc : 0 < (n.factorial : ℝ) * (2 / p) ^ n :=
    mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (pow_pos (div_pos two_pos hp) n)
  have hroot := hscaled.rpow_const (p := 1 / p) (Or.inl hc.ne')
  apply Filter.Tendsto.congr' _ hroot
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
  have hM : 0 < complexSphereMellin n (m * p / 2) := by
    apply complexBlockSphereMellin_pos
    have hmp : 0 < m * p / 2 := div_pos (mul_pos hm hp) two_pos
    linarith only [hmp]
  rw [Real.mul_rpow (pow_nonneg hm.le _) hM.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
  change m ^ ((n : ℝ) * (1 / p)) * complexSphereMonomialNorm n p m = _
  rw [mul_one_div]

/-- The `Lᵠ/Lᵖ` ratio has a precise polynomial concentration rate. -/
theorem tendsto_complexSphereMonomialNorm_ratio (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun m : ℝ => m ^ (-((n : ℝ) * (1 / p - 1 / q))) *
      (complexSphereMonomialNorm n q m / complexSphereMonomialNorm n p m)) atTop
        (𝓝 (complexSphereMonomialConstant n q / complexSphereMonomialConstant n p)) := by
  have h := (tendsto_complexSphereMonomialNorm_scaled n hq).div
    (tendsto_complexSphereMonomialNorm_scaled n hp) (complexSphereMonomialConstant_pos n hp).ne'
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
  rw [mul_div_mul_comm, ← Real.rpow_sub hm]
  congr 2
  ring

/-- In complex dimension at least two, increasing the exponent gives an unbounded norm ratio. -/
theorem tendsto_complexSphereMonomialNorm_ratio_atTop {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    Tendsto (fun m : ℝ =>
      complexSphereMonomialNorm n q m / complexSphereMonomialNorm n p m) atTop atTop := by
  have hq : 0 < q := hp.trans hpq
  have he : 0 < (n : ℝ) * (1 / p - 1 / q) :=
    mul_pos (Nat.cast_pos.mpr hn) (sub_pos.mpr (one_div_lt_one_div_of_lt hp hpq))
  have h := (tendsto_complexSphereMonomialNorm_ratio n hp hq).pos_mul_atTop
    (div_pos (complexSphereMonomialConstant_pos n hq) (complexSphereMonomialConstant_pos n hp))
    (tendsto_rpow_atTop he)
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with m hm
  calc
    _ = (m ^ (-((n : ℝ) * (1 / p - 1 / q))) *
        m ^ ((n : ℝ) * (1 / p - 1 / q))) *
          (complexSphereMonomialNorm n q m / complexSphereMonomialNorm n p m) := by ring
    _ = _ := by rw [← Real.rpow_add hm, neg_add_cancel, Real.rpow_zero, one_mul]

/-- No degree-independent reverse `Lᵖ` comparison holds even for coordinate monomials. -/
theorem not_uniform_complexSphereMonomialNorm {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ¬ ∃ C : ℝ, ∀ m : ℕ,
      complexSphereMonomialNorm n q m ≤ C * complexSphereMonomialNorm n p m := by
  rintro ⟨C, hC⟩
  have h := (tendsto_complexSphereMonomialNorm_ratio_atTop hn hp hpq).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨m, hm⟩ := (h.eventually_gt_atTop C).exists
  have hpos := complexSphereMonomialNorm_pos n hp (Nat.cast_nonneg m)
  exact (not_lt_of_ge ((div_le_iff₀ hpos).mpr (hC m))) hm

/-- Lower exponent in the critical Cauchy--Riemann Sobolev pair. -/
def complexSphereCarlemanP (n : ℕ) : ℝ :=
  4 * ((n : ℝ) + 1) / (2 * ((n : ℝ) + 1) + 1)

/-- Upper exponent in the critical Cauchy--Riemann Sobolev pair. -/
def complexSphereCarlemanQ (n : ℕ) : ℝ :=
  4 * ((n : ℝ) + 1) / (2 * ((n : ℝ) + 1) - 1)

theorem complexSphereCarlemanP_pos (n : ℕ) : 0 < complexSphereCarlemanP n := by
  unfold complexSphereCarlemanP
  positivity

theorem complexSphereCarlemanP_lt_Q (n : ℕ) :
    complexSphereCarlemanP n < complexSphereCarlemanQ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold complexSphereCarlemanP complexSphereCarlemanQ
  apply (div_lt_div_iff₀ (by positivity) (by linarith only [hn])).mpr
  nlinarith only [hn]

/-- The critical exponent pair gives concentration rate `n / (2(n+1))`. -/
theorem complexSphereCarleman_exponent (n : ℕ) :
    (n : ℝ) * (1 / complexSphereCarlemanP n - 1 / complexSphereCarlemanQ n) =
      (n : ℝ) / (2 * ((n : ℝ) + 1)) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold complexSphereCarlemanP complexSphereCarlemanQ
  field_simp
  ring

/-- The angular part of the radial Carleman obstruction, with its exact leading constant. -/
theorem tendsto_complexSphereCarleman_ratio (n : ℕ) :
    Tendsto (fun m : ℝ => m ^ (-((n : ℝ) / (2 * ((n : ℝ) + 1)))) *
      (complexSphereMonomialNorm n (complexSphereCarlemanQ n) m /
        complexSphereMonomialNorm n (complexSphereCarlemanP n) m)) atTop
      (𝓝 (complexSphereMonomialConstant n (complexSphereCarlemanQ n) /
        complexSphereMonomialConstant n (complexSphereCarlemanP n))) := by
  have hp := complexSphereCarlemanP_pos n
  have hq := hp.trans (complexSphereCarlemanP_lt_Q n)
  simpa only [complexSphereCarleman_exponent] using
    tendsto_complexSphereMonomialNorm_ratio n hp hq

end GaloisForLFunctions.HTGeometry
