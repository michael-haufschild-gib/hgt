import GaloisForLFunctions.HTGeometry.ImproperAntitoneRiemannSum
import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue

/-!
# Exact positive-shift Hurwitz and polygamma asymptotics

The scale-free identity

`x^q ∑_{n≥0} (x+n)^(-(q+1)) → 1/q`

is proved directly from the sharp real-mesh integral-test squeeze.  The Hurwitz value bridge then
gives the exact leading constant of every positive-order polygamma derivative.  No sectorial
Stirling expansion or asymptotic axiom is used.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set MeasureTheory

noncomputable section

/-- The real positive-shift power tail underlying integer-exponent Hurwitz values. -/
def shiftedPowerTail (q : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + x) ^ (-(q + 1 : ℝ))

/-- Exact continuum limit of a positive-shift power tail. -/
theorem tendsto_scaled_shiftedPowerTail (q : ℕ) (hq : 0 < q) :
    Tendsto (fun x : ℝ => x ^ q * shiftedPowerTail q x) atTop
      (nhds (1 / (q : ℝ))) := by
  let f : ℝ → ℝ := fun u => (1 + u) ^ (-(q + 1 : ℝ))
  have hq1 : (1 : ℝ) < q + 1 := by exact_mod_cast Nat.lt_add_one_iff.mpr hq
  have hanti : AntitoneOn f (Ici 0) := by
    intro a ha b hb hab
    have ha0 : 0 ≤ a := ha
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hnn : ∀ u ∈ Ici (0 : ℝ), 0 ≤ f u := by
    intro u hu
    have hu0 : 0 ≤ u := hu
    exact Real.rpow_nonneg (by linarith) _
  have hint : IntegrableOn f (Ioi 0) := by
    dsimp [f]
    have h : (fun x : ℝ => (1 + x) ^ (-(q + 1 : ℝ))) =
        (fun x : ℝ => (x + 1) ^ (-(q + 1 : ℝ))) := by
      funext x
      rw [add_comm]
    rw [h]
    rw [show Ioi (0 : ℝ) = (fun x : ℝ => x + 1) ⁻¹' Ioi 1 by ext x; simp]
    exact ((measurePreserving_add_right (volume : Measure ℝ) 1).integrableOn_comp_preimage
        (measurableEmbedding_addRight 1)).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num))
  have hlim := HTGeometry.tendsto_realMesh_antitone_Ioi hanti hnn hint
  have hintValue : ∫ u in Ioi (0 : ℝ), f u = 1 / (q : ℝ) := by
    dsimp [f]
    have hshift : ∫ u in Ioi (0 : ℝ), (1 + u) ^ (-(q + 1 : ℝ))
        = ∫ t in Ioi (1 : ℝ), t ^ (-(q + 1 : ℝ)) := by
      have hmp := measurePreserving_add_right (volume : Measure ℝ) 1
      have h := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight 1)
        (fun t : ℝ => t ^ (-(q + 1 : ℝ))) (Ioi (1 : ℝ))
      rw [show (fun x : ℝ => x + 1) ⁻¹' Ioi 1 = Ioi 0 by ext x; simp] at h
      simpa [add_comm] using h
    rw [hshift, integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
    rw [Real.one_rpow]
    have hden : -(q + 1 : ℝ) + 1 = -(q : ℝ) := by ring
    rw [hden, div_neg]
    ring
  rw [hintValue] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hterm : ∀ n : ℕ,
      (1 / x) * f ((n : ℝ) / x) =
        x ^ q * (((n : ℝ) + x) ^ (-(q + 1 : ℝ))) := by
    intro n
    dsimp [f]
    have hnx : 0 < (n : ℝ) + x := by positivity
    rw [show 1 + (n : ℝ) / x = ((n : ℝ) + x) / x by field_simp; ring]
    rw [Real.div_rpow hnx.le hx.le, Real.rpow_neg hx.le, div_inv_eq_mul]
    rw [show (q + 1 : ℝ) = (q : ℝ) + 1 by ring,
      Real.rpow_add hx, Real.rpow_natCast, Real.rpow_one]
    field_simp
  rw [shiftedPowerTail]
  calc
    (1 / x) * ∑' k : ℕ, f ((k : ℝ) / x) =
        ∑' k : ℕ, (1 / x) * f ((k : ℝ) / x) := (tsum_mul_left).symm
    _ = ∑' k : ℕ, x ^ q * (((k : ℝ) + x) ^ (-(q + 1 : ℝ))) :=
      tsum_congr hterm
    _ = x ^ q * ∑' k : ℕ, (((k : ℝ) + x) ^ (-(q + 1 : ℝ))) := tsum_mul_left

/-- On the positive real axis, the integer-exponent complex Hurwitz value is exactly the cast of
the real shifted power tail. -/
theorem hzeta_nat_ofReal_eq_shiftedPowerTail (q : ℕ) {x : ℝ} (hx : 0 < x) :
    HurwitzZetaShift.hzeta ((q + 1 : ℕ) : ℂ) (x : ℂ) =
      (shiftedPowerTail q x : ℂ) := by
  rw [HurwitzZetaShift.hzeta, shiftedPowerTail, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  have hnx : 0 ≤ (n : ℝ) + x := by positivity
  rw [show (n : ℂ) + (x : ℂ) = (((n : ℝ) + x : ℝ) : ℂ) by push_cast; ring]
  rw [show -((q + 1 : ℕ) : ℂ) = ((-(q + 1 : ℝ) : ℝ) : ℂ) by push_cast; ring]
  exact (Complex.ofReal_cpow hnx _).symm

/-- Exact scaled positive-shift Hurwitz asymptotic at every positive integer exponent. -/
theorem tendsto_scaled_hzeta_nat_ofReal (q : ℕ) (hq : 0 < q) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ q *
        HurwitzZetaShift.hzeta ((q + 1 : ℕ) : ℂ) (x : ℂ))
      atTop (nhds ((1 / (q : ℝ) : ℝ) : ℂ)) := by
  have h := Filter.Tendsto.comp Complex.continuous_ofReal.continuousAt
    (tendsto_scaled_shiftedPowerTail q hq)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [hzeta_nat_ofReal_eq_shiftedPowerTail q hx]
  norm_cast

/-- Every positive-order polygamma derivative has its exact first large-real-axis term:
`x^q ψ⁽ܗ⁾(x) → (-1)^(q+1) (q-1)!`. -/
theorem tendsto_scaled_polygamma_ofReal (q : ℕ) (hq : 0 < q) :
    Tendsto
      (fun x : ℝ => (x : ℂ) ^ q *
        iteratedDeriv q Complex.digamma (x : ℂ))
      atTop
      (nhds ((-1 : ℂ) ^ (q + 1) * ((q - 1).factorial : ℂ))) := by
  have hz := tendsto_scaled_hzeta_nat_ofReal q hq
  have hscaled := hz.const_mul
    ((-1 : ℂ) ^ (q + 1) * (q.factorial : ℂ))
  have hlim :
      ((-1 : ℂ) ^ (q + 1) * (q.factorial : ℂ)) *
          ((1 / (q : ℝ) : ℝ) : ℂ) =
        (-1 : ℂ) ^ (q + 1) * ((q - 1).factorial : ℂ) := by
    rw [← Nat.mul_factorial_pred (ne_of_gt hq)]
    push_cast
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
    field_simp [hq0]
  rw [hlim] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hpoly := polygamma_eq_hzeta (q - 1) (z := (x : ℂ)) (by simpa using hx)
  rw [show q - 1 + 1 = q by omega] at hpoly
  rw [hpoly, show q - 1 + 2 = q + 1 by omega]
  ring

end

end GaloisForLFunctions
