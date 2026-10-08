import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBoundaryTransport

/-! # The actual finite Poisson packet satisfies both modular boundary identities -/

noncomputable section

open Set Complex Filter Topology Polynomial ComplexConjugate

namespace RHTower.WeilHigherDenominator

open MaassBesselSeries

private lemma boundaryLine_tendsto (x : ℝ) :
    Tendsto (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  have hy : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hy.mul_const I)

private lemma fractional_im {z : ℂ} (hz1 : z + 1 ≠ 0) :
    (z / (z + 1)).im = z.im / normSq (z + 1) := by
  have he : z / (z + 1) = 1 + invS (z + 1) := by
    dsimp [invS]
    field_simp
    ring
  rw [he, add_im, one_im, zero_add, invS_im]
  simp

/-- The spatial three-term identity transports to the precise weight-one boundary identity. -/
theorem poissonPacket_boundary_three_term (Z : Finset ℂ) (R : ℂ → ℂ[X])
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (hthree : ∀ z : ℂ, 0 < z.im →
      (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z) =
        (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z + 1)) +
          ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z / (z + 1))) :
    ∀ x > 0, finitePoleBoundary Z id R x = finitePoleBoundary Z id R (x + 1) +
      finitePoleBoundary Z id R (x / (x + 1)) / ((x + 1 : ℝ) : ℂ) := by
  intro x hx
  let z : ℝ → ℂ := fun y => (x : ℂ) + (y : ℂ) * I
  have hz := boundaryLine_tendsto x
  have hx1 : 0 < x + 1 := by linarith
  have hx1c : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast hx1.ne'
  have hz1 (y : ℝ) : z y + 1 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp [z] at this
    linarith
  have hbase := poissonPacket_boundary_path (z := z) (d := fun _ => 1) Z R hstrip hx zero_lt_one
    (by simpa only [ofReal_re, Function.comp_def] using continuous_re.continuousAt.tendsto.comp hz)
    (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)) tendsto_const_nhds
    (Eventually.of_forall fun y => by simp [z])
  have hplus := poissonPacket_boundary_path (z := fun y => z y + 1) (d := fun _ => 1)
    Z R hstrip hx1 zero_lt_one
    (by simpa only [z, add_re, ofReal_re, one_re, Function.comp_def] using
      continuous_re.continuousAt.tendsto.comp (hz.add_const 1))
    (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)) tendsto_const_nhds
    (Eventually.of_forall fun y => by simp [z])
  have hf := hz.div (hz.add_const 1) hx1c
  have hfre : Tendsto (fun y => (z y / (z y + 1)).re) (𝓝[>] 0)
      (𝓝 (x / (x + 1))) := by
    convert continuous_re.continuousAt.tendsto.comp hf using 1 <;>
      simp [z, Function.comp_def, Pi.div_apply, ← ofReal_one, ← ofReal_add, ← ofReal_div]
  have hd : Tendsto (fun y => normSq (z y + 1)) (𝓝[>] 0) (𝓝 ((x + 1) ^ 2)) := by
    have hh := continuous_normSq.continuousAt.tendsto.comp (hz.add_const 1)
    convert hh using 1 <;> simp [z, Function.comp_def, normSq_apply, pow_two]
  have hfrac := poissonPacket_boundary_path Z R hstrip (div_pos hx hx1)
    (sq_pos_of_pos hx1) hfre
    (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)) hd
    (Eventually.of_forall fun y => by rw [fractional_im (hz1 y)]; simp [z])
  simp only [Real.sqrt_one, ofReal_one, div_one] at hbase hplus
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hx1] at hfrac
  have he := hplus.add hfrac
  have hh : (fun y : ℝ =>
      (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z y + 1)) /
          ((Real.sqrt y : ℂ) * (Real.log y : ℂ)) +
        (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z y / (z y + 1))) /
          ((Real.sqrt y : ℂ) * (Real.log y : ℂ))) =ᶠ[𝓝[>] 0]
      (fun y => (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z y)) /
        ((Real.sqrt y : ℂ) * (Real.log y : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [← add_div, ← hthree (z y) (by simpa [z] using hy)]
  have hhlim := tendsto_nhds_unique hbase (he.congr' hh)
  linear_combination hhlim / (-2 : ℂ)

/-- Odd spatial inversion gives the odd weight-one boundary identity. -/
theorem poissonPacket_boundary_inversion (Z : Finset ℂ) (R : ℂ → ℂ[X])
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (hinv : ∀ z : ℂ, 0 < z.im →
      (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (invS z)) =
        -(∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z)) :
    ∀ x > 0, finitePoleBoundary Z id R x = -finitePoleBoundary Z id R x⁻¹ / (x : ℂ) := by
  intro x hx
  let z : ℝ → ℂ := fun y => (x : ℂ) + (y : ℂ) * I
  let w : ℝ → ℂ := fun y => -conj (invS (z y))
  have hz := boundaryLine_tendsto x
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hw : Tendsto w (𝓝[>] 0) (𝓝 ((x⁻¹ : ℝ) : ℂ)) := by
    have hh := (continuous_conj.continuousAt.tendsto.comp ((hz.inv₀ hxc).neg)).neg
    simpa only [Function.comp_def, invS, map_neg, map_inv₀, conj_ofReal, neg_neg, ofReal_inv, w, z] using hh
  have hd : Tendsto (fun y => normSq (z y)) (𝓝[>] 0) (𝓝 (x ^ 2)) := by
    have hh := continuous_normSq.continuousAt.tendsto.comp hz
    convert hh using 1 <;> simp [z, Function.comp_def, normSq_apply, pow_two]
  have hbase := poissonPacket_boundary_path (z := z) (d := fun _ => 1) Z R hstrip hx zero_lt_one
    (by simpa only [ofReal_re, Function.comp_def] using continuous_re.continuousAt.tendsto.comp hz)
    (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)) tendsto_const_nhds
    (Eventually.of_forall fun y => by simp [z])
  have hi := poissonPacket_boundary_path (z := w) Z R hstrip (inv_pos.mpr hx) (sq_pos_of_pos hx)
    (by simpa only [ofReal_re, Function.comp_def] using continuous_re.continuousAt.tendsto.comp hw)
    (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)) hd
    (Eventually.of_forall fun y => by simp only [w, neg_im, conj_im, neg_neg, invS_im]; simp [z])
  simp only [Real.sqrt_one, ofReal_one, div_one] at hbase
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hx] at hi
  have he : (fun y : ℝ => (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (w y)) /
      ((Real.sqrt y : ℂ) * (Real.log y : ℂ))) =ᶠ[𝓝[>] 0]
      (fun y => -((∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z y)) /
        ((Real.sqrt y : ℂ) * (Real.log y : ℂ)))) := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    simp only [w, polynomialPolarMode_reflect]
    rw [hinv (z y) (by simpa [z] using hy), neg_div]
  have hhlim := tendsto_nhds_unique (hi.congr' he) hbase.neg
  linear_combination hhlim / (-2 : ℂ)

/-- Both actual spatial identities exclude every nonzero finite polynomial Poisson packet. -/
theorem poissonPacket_eq_zero_of_period (Z : Finset ℂ) (R : ℂ → ℂ[X])
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (hthree : ∀ z : ℂ, 0 < z.im →
      (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z) =
        (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z + 1)) +
          ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z / (z + 1)))
    (hinv : ∀ z : ℂ, 0 < z.im →
      (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (invS z)) =
        -(∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z)) :
    ∀ ρ ∈ Z, R ρ = 0 :=
  finitePoleBoundary_eq_zero_of_period Z id (fun _ _ _ _ h => h)
    (fun ρ hρ => (hstrip ρ hρ).1) R
    (poissonPacket_boundary_three_term Z R hstrip hthree)
    (poissonPacket_boundary_inversion Z R hstrip hinv)

/-- Translation invariance alone supplies both spatial identities for an actual defect packet. -/
theorem poissonPacket_eq_zero_of_inversionDefect (Z : Finset ℂ) (R : ℂ → ℂ[X])
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    {u : ℂ → ℂ} (hper : Function.Periodic u 1)
    (hpacket : ∀ z : ℂ, 0 < z.im → u z - u (invS z) =
      ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z) :
    ∀ ρ ∈ Z, R ρ = 0 := by
  have he (z : ℂ) (hz : 0 < z.im) : inversionDefect u z =
      ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z := hpacket z hz
  apply poissonPacket_eq_zero_of_period Z R hstrip
  · intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_upper hz
    have hz1 : z + 1 ≠ 0 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    have hfrac : 0 < (z / (z + 1)).im := by
      rw [fractional_im hz1]
      exact div_pos hz (normSq_pos.mpr hz1)
    rw [← he z hz, ← he (z + 1) (by simpa using hz), ← he _ hfrac]
    exact inversionDefect_three_term hper hz0 hz1
  · intro z hz
    rw [← he (invS z) (invS_mem_upper hz), ← he z hz]
    exact inversionDefect_inv u z

end RHTower.WeilHigherDenominator
