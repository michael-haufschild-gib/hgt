import GaloisForLFunctions.RHTower.SelbergCuspLeftLineDecay

/-!
# Gamma decay for the ordinary Mellin transform below degree one

The ordinary exponential series uses shifts by integers. Its reflected Gamma
product has total slope equal to the Selberg degree, whereas the Mellin Gamma
denominator has slope one. Below degree one the quotient therefore decays
faster than every geometric sequence.
-/

noncomputable section
open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass

private theorem gammaProduct_root_tendsto_zero
    {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hsum : ∑ i, c i < 1) (β : ι → ℂ) :
    Tendsto (fun k : ℕ => ((∏ i, ‖Complex.Gamma (((c i * (k : ℝ) : ℝ) : ℂ) + β i)‖) /
      (k.factorial : ℝ)) ^ (1 / (k : ℝ))) atTop (𝓝 0) := by
  classical
  have hP := tendsto_finsetProd Finset.univ (fun i _ =>
    tendsto_norm_Gamma_linear_rpow_inv_nat (hc i) (β i))
  have hpow : Tendsto (fun k : ℕ => (k : ℝ) ^ ((∑ i, c i) - 1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr hsum)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1 <;> simp [sub_eq_add_neg]
  have hlim := (hP.mul tendsto_div_factorial_rpow_inv).mul hpow
  simp only [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  rw [Real.div_rpow (Finset.prod_nonneg fun i _ => norm_nonneg _) hfact.le,
    ← Real.finsetProd_rpow _ _ (fun i _ => norm_nonneg _),
    Finset.prod_div_distrib, prod_rpow_const _ hkpos c,
    Real.rpow_sub hkpos, Real.rpow_one]
  have hkc : (k : ℝ) ^ (∑ i, c i) ≠ 0 := (Real.rpow_pos_of_pos hkpos _).ne'
  have hfr : (k.factorial : ℝ) ^ (1 / (k : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hfact _).ne'
  field_simp

/-- Each Gamma scale occurs twice in the reflected ordinary Mellin kernel. -/
def ordinaryGammaRate (D : RHTower.SelbergGammaData) : Fin D.rank ⊕ Fin D.rank → ℝ :=
  Sum.elim D.lambda D.lambda

theorem ordinaryGammaRate_pos (D : RHTower.SelbergGammaData)
    (i : Fin D.rank ⊕ Fin D.rank) : 0 < ordinaryGammaRate D i := by
  cases i with
  | inl j => exact D.lambda_pos j
  | inr j => exact D.lambda_pos j

/-- The ordinary Gamma slopes sum to the presentation degree. -/
theorem sum_ordinaryGammaRate (D : RHTower.SelbergGammaData) :
    ∑ i, ordinaryGammaRate D i = D.degree := by
  rw [Fintype.sum_sum_type]
  change (∑ j, D.lambda j) + (∑ j, D.lambda j) = 2 * ∑ j, D.lambda j
  ring

/-- Real-part Gamma majorant on the line `Re u = -k-1/2`. -/
def ordinaryGammaProduct (D : RHTower.SelbergGammaData) (s : ℂ) (k : ℕ) : ℝ :=
  ∏ i, ‖Complex.Gamma (((ordinaryGammaRate D i * k : ℝ) : ℂ) +
    ((D.pairShift (s - 1 / 2) i).re : ℂ))‖

theorem ordinaryGammaProduct_nonneg (D : RHTower.SelbergGammaData) (s : ℂ) (k : ℕ) :
    0 ≤ ordinaryGammaProduct D s k := Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- Below degree one, the ordinary Gamma majorant divided by the Mellin Gamma
denominator has root limit zero. -/
theorem ordinaryGammaProduct_div_Gamma_root_tendsto_zero
    (D : RHTower.SelbergGammaData) (hD : D.degree < 1) (s : ℂ) :
    Tendsto (fun k : ℕ => (ordinaryGammaProduct D s k /
      Real.Gamma ((k : ℝ) + 3 / 2)) ^ (1 / (k : ℝ))) atTop (𝓝 0) := by
  have hP := gammaProduct_root_tendsto_zero (ordinaryGammaRate_pos D)
    (by rwa [sum_ordinaryGammaRate]) (fun i => ((D.pairShift (s - 1 / 2) i).re : ℂ))
  have hlim := hP.mul RHTower.tendsto_factorial_div_Gamma_three_halves_rpow_inv
  simp only [zero_mul] at hlim
  refine hlim.congr fun k => ?_
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hΓ : 0 < Real.Gamma ((k : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  change (ordinaryGammaProduct D s k / (k.factorial : ℝ)) ^ (1 / (k : ℝ)) *
    ((k.factorial : ℝ) / Real.Gamma ((k : ℝ) + 3 / 2)) ^ (1 / (k : ℝ)) = _
  rw [← Real.mul_rpow (div_nonneg (ordinaryGammaProduct_nonneg D s k) hfact.le)
    (div_nonneg hfact.le hΓ.le)]
  congr 1
  field_simp

end GaloisForLFunctions.SelbergClass
