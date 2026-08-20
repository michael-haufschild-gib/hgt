/-
# The archimedean root of the degree-`d` shift lattice

Along the lattice `s₀ - k/d` the archimedean factor of the asymmetric functional equation is a
constant, a power of `Q` advancing at rate `2/d`, and `2r` Gamma values advancing at rates
`λ_j/d` whose total is one.  The Gamma product law then gives the `k`-th root of the normalized
factor exactly, and it is the cusp constant `q^{1/d}/(2πd)` of the gamma presentation.

Main results:
* `SelbergGammaData.pairRate`, `pairShift` — the `2r` rates and constant shifts.
* `SelbergGammaData.sum_pairRate` — the rates sum to one, by the definition of the degree.
* `SelbergGammaData.norm_asymmetricH_shift` — the modulus of the archimedean factor.
* `SelbergGammaData.archimedeanRootConstant_eq` — the root constant is `q^{1/d}/(2πd)`.
* `SelbergGammaData.tendsto_norm_asymmetricH_shift_rpow_inv` —
  **`(‖h_F(s₀-k/d)‖/k!)^{1/k} → q^{1/d}/(2πd)`**.
-/
import GaloisForLFunctions.RHTower.SelbergClass.AsymmetricFunctionalEquation
import GaloisForLFunctions.HTGeometry.GammaProductRootLaw

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Rates and shifts of the archimedean Gamma factors -/

/-- The rate at which the `j`-th Gamma argument advances along the degree-`d` shift lattice. -/
def SelbergGammaData.shiftRate (G : SelbergGammaData) (j : Fin G.rank) : ℝ :=
  G.lambda j / G.degree

/-- The constant part of the `j`-th upper Gamma argument. -/
def SelbergGammaData.shiftUp (G : SelbergGammaData) (s₀ : ℂ) (j : Fin G.rank) : ℂ :=
  (G.lambda j : ℂ) * (1 - s₀) + star (G.mu j)

/-- The constant part of the `j`-th lower Gamma argument. -/
def SelbergGammaData.shiftDown (G : SelbergGammaData) (s₀ : ℂ) (j : Fin G.rank) : ℂ :=
  1 - (G.lambda j : ℂ) * s₀ - G.mu j

/-- The `2r` rates of the archimedean factor. -/
def SelbergGammaData.pairRate (G : SelbergGammaData) : Fin G.rank ⊕ Fin G.rank → ℝ :=
  Sum.elim G.shiftRate G.shiftRate

/-- The `2r` constant shifts of the archimedean factor. -/
def SelbergGammaData.pairShift (G : SelbergGammaData) (s₀ : ℂ) :
    Fin G.rank ⊕ Fin G.rank → ℂ :=
  Sum.elim (G.shiftUp s₀) (G.shiftDown s₀)

theorem SelbergGammaData.shiftRate_pos (G : SelbergGammaData) (hd : 0 < G.degree)
    (j : Fin G.rank) : 0 < G.shiftRate j :=
  div_pos (G.lambda_pos j) hd

theorem SelbergGammaData.pairRate_pos (G : SelbergGammaData) (hd : 0 < G.degree)
    (i : Fin G.rank ⊕ Fin G.rank) : 0 < G.pairRate i := by
  cases i with
  | inl j => exact G.shiftRate_pos hd j
  | inr j => exact G.shiftRate_pos hd j

/-- **The rates sum to one** — this is the definition of the degree. -/
theorem SelbergGammaData.sum_pairRate (G : SelbergGammaData) (hd : 0 < G.degree) :
    ∑ i, G.pairRate i = 1 := by
  have hsplit : ∑ j, G.shiftRate j = (∑ j, G.lambda j) / G.degree := by
    unfold SelbergGammaData.shiftRate
    rw [Finset.sum_div]
  have hdeg : G.degree = 2 * ∑ j, G.lambda j := rfl
  have hsum : ∑ i, G.pairRate i = ∑ j, G.shiftRate j + ∑ j, G.shiftRate j := by
    rw [Fintype.sum_sum_type]
    rfl
  have hcomb : (∑ j, G.lambda j) / G.degree + (∑ j, G.lambda j) / G.degree
      = (2 * ∑ j, G.lambda j) / G.degree := by ring
  rw [hsum, hsplit, hcomb, ← hdeg, div_self hd.ne']

/-! ## The two Gamma arguments along the lattice -/

theorem SelbergGammaData.gammaArg_up_shift (G : SelbergGammaData) (hd : 0 < G.degree) (s₀ : ℂ)
    (k : ℕ) (j : Fin G.rank) :
    (G.lambda j : ℂ) * (1 - (s₀ - (k : ℂ) / (G.degree : ℂ))) + star (G.mu j)
      = ((G.shiftRate j * (k : ℝ) : ℝ) : ℂ) + G.shiftUp s₀ j := by
  have hdne : (G.degree : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  unfold SelbergGammaData.shiftRate SelbergGammaData.shiftUp
  push_cast
  field_simp
  ring

theorem SelbergGammaData.gammaArg_down_shift (G : SelbergGammaData) (hd : 0 < G.degree) (s₀ : ℂ)
    (k : ℕ) (j : Fin G.rank) :
    1 - (G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) - G.mu j
      = ((G.shiftRate j * (k : ℝ) : ℝ) : ℂ) + G.shiftDown s₀ j := by
  have hdne : (G.degree : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  unfold SelbergGammaData.shiftRate SelbergGammaData.shiftDown
  push_cast
  field_simp
  ring

/-! ## The modulus of the archimedean factor -/

theorem SelbergGammaData.norm_asymmetricH_shift (G : SelbergGammaData) (hd : 0 < G.degree)
    (s₀ : ℂ) (k : ℕ) :
    ‖G.asymmetricH (s₀ - (k : ℂ) / (G.degree : ℂ))‖
      = ((2 * Real.pi) ^ G.rank)⁻¹
        * G.Q ^ ((1 - 2 * s₀.re) + 2 / G.degree * (k : ℝ))
        * ∏ i, ‖Complex.Gamma (((G.pairRate i * (k : ℝ) : ℝ) : ℂ) + G.pairShift s₀ i)‖ := by
  have hpi : ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have h1 : ‖((2 * Real.pi : ℂ) ^ G.rank)⁻¹‖ = ((2 * Real.pi) ^ G.rank)⁻¹ := by
    rw [norm_inv, norm_pow, hpi, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have h2 : ‖∏ j, (G.lambda j : ℂ) ^ ((2 : ℂ) * Complex.I * (((G.mu j).im : ℝ) : ℂ))‖ = 1 := by
    rw [norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    have hre : ((2 : ℂ) * Complex.I * (((G.mu j).im : ℝ) : ℂ)).re = 0 := by simp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (G.lambda_pos j), hre, Real.rpow_zero]
  have hkd : ((k : ℂ) / (G.degree : ℂ)) = ((((k : ℝ) / G.degree : ℝ)) : ℂ) := by
    push_cast
    ring
  have h3 : ‖(G.Q : ℂ) ^ (1 - 2 * (s₀ - (k : ℂ) / (G.degree : ℂ)))‖
      = G.Q ^ ((1 - 2 * s₀.re) + 2 / G.degree * (k : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos G.Q_pos]
    congr 1
    have hz : (1 : ℂ) - 2 * (s₀ - (((k : ℝ) / G.degree : ℝ) : ℂ))
        = (1 - 2 * s₀) + ((2 * ((k : ℝ) / G.degree) : ℝ) : ℂ) := by push_cast; ring
    rw [hkd, hz, Complex.add_re, Complex.ofReal_re]
    have h2s : ((1 : ℂ) - 2 * s₀).re = 1 - 2 * s₀.re := by simp
    rw [h2s]
    ring
  have h4 : ‖∏ j, Complex.Gamma ((G.lambda j : ℂ) * (1 - (s₀ - (k : ℂ) / (G.degree : ℂ)))
        + star (G.mu j))
        * Complex.Gamma (1 - (G.lambda j : ℂ) * (s₀ - (k : ℂ) / (G.degree : ℂ)) - G.mu j)‖
      = ∏ i, ‖Complex.Gamma (((G.pairRate i * (k : ℝ) : ℝ) : ℂ) + G.pairShift s₀ i)‖ := by
    rw [norm_prod, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [norm_mul, G.gammaArg_up_shift hd s₀ k j, G.gammaArg_down_shift hd s₀ k j]
    rfl
  unfold SelbergGammaData.asymmetricH
  rw [norm_mul, norm_mul, norm_mul, h1, h2, h3, h4]
  ring

/-! ## The root constant -/

/-- **The archimedean root constant is the cusp constant of the gamma presentation.** -/
theorem SelbergGammaData.archimedeanRootConstant_eq (G : SelbergGammaData) (hd : 0 < G.degree) :
    G.Q ^ (2 / G.degree) * (∏ i, (G.pairRate i) ^ (G.pairRate i))
      = G.conductor ^ (1 / G.degree) / (2 * Real.pi * G.degree) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlam : ∀ j, (0 : ℝ) < G.lambda j := G.lambda_pos
  -- the left-hand product
  have hleft : (∏ i, (G.pairRate i) ^ (G.pairRate i))
      = (∏ j, G.lambda j ^ (2 * G.lambda j / G.degree)) / G.degree := by
    have hstep : ∀ j : Fin G.rank,
        G.shiftRate j ^ G.shiftRate j * G.shiftRate j ^ G.shiftRate j
          = G.lambda j ^ (2 * G.lambda j / G.degree) / G.degree ^ (2 * G.lambda j / G.degree) := by
      intro j
      rw [← Real.rpow_add (G.shiftRate_pos hd j)]
      show (G.lambda j / G.degree) ^ (G.lambda j / G.degree + G.lambda j / G.degree) = _
      rw [show G.lambda j / G.degree + G.lambda j / G.degree = 2 * G.lambda j / G.degree from by
        ring]
      exact Real.div_rpow (hlam j).le hd.le _
    have hexp : (∏ i, (G.pairRate i) ^ (G.pairRate i))
        = ∏ j, (G.shiftRate j ^ G.shiftRate j * G.shiftRate j ^ G.shiftRate j) := by
      rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
      rfl
    have hstep2 : (∏ j, (G.shiftRate j ^ G.shiftRate j * G.shiftRate j ^ G.shiftRate j))
        = ∏ j, (G.lambda j ^ (2 * G.lambda j / G.degree)
          / G.degree ^ (2 * G.lambda j / G.degree)) :=
      Finset.prod_congr rfl fun j _ => hstep j
    have hsum : ∑ j, 2 * G.lambda j / G.degree = 1 := by
      have hdeg : G.degree = 2 * ∑ j, G.lambda j := rfl
      have hcomb : ∑ j, 2 * G.lambda j / G.degree = (2 * ∑ j, G.lambda j) / G.degree := by
        rw [Finset.mul_sum, Finset.sum_div]
      rw [hcomb, ← hdeg, div_self hd.ne']
    rw [hexp, hstep2, Finset.prod_div_distrib,
      prod_rpow_const _ hd (fun j => 2 * G.lambda j / G.degree), hsum, Real.rpow_one]
  -- the right-hand side
  have hcond : G.conductor ^ (1 / G.degree)
      = 2 * Real.pi * G.Q ^ (2 / G.degree) * ∏ j, G.lambda j ^ (2 * G.lambda j / G.degree) := by
    unfold SelbergGammaData.conductor
    have hp1 : (0 : ℝ) ≤ (2 * Real.pi) ^ G.degree := (Real.rpow_pos_of_pos hpi _).le
    have hp2 : (0 : ℝ) ≤ G.Q ^ 2 := by positivity
    have hp3 : (0 : ℝ) ≤ ∏ j, G.lambda j ^ (2 * G.lambda j) :=
      Finset.prod_nonneg fun j _ => (Real.rpow_pos_of_pos (hlam j) _).le
    rw [Real.mul_rpow (by positivity) hp3, Real.mul_rpow hp1 hp2]
    congr 1
    · congr 1
      · rw [← Real.rpow_mul hpi.le, mul_one_div, div_self hd.ne', Real.rpow_one]
      · rw [← Real.rpow_natCast G.Q 2, ← Real.rpow_mul G.Q_pos.le]
        congr 1
        push_cast
        ring
    · rw [← Real.finsetProd_rpow _ _ (fun j _ => (Real.rpow_pos_of_pos (hlam j) _).le)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Real.rpow_mul (hlam j).le]
      congr 1
      ring
  rw [hleft, hcond]
  field_simp

/-! ## The root law -/

theorem tendsto_rpow_linear_rpow_inv {Q a b : ℝ} (hQ : 0 < Q) :
    Tendsto (fun k : ℕ => (Q ^ (a + b * (k : ℝ))) ^ (1 / (k : ℝ))) atTop (𝓝 (Q ^ b)) := by
  have hcont : Tendsto (fun t : ℝ => Q ^ t) (𝓝 b) (𝓝 (Q ^ b)) := by
    have hrw : (fun t : ℝ => Q ^ t) = fun t : ℝ => Real.exp (Real.log Q * t) :=
      funext fun t => Real.rpow_def_of_pos hQ t
    rw [hrw, Real.rpow_def_of_pos hQ]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto b
  have hexp : Tendsto (fun k : ℕ => (a + b * (k : ℝ)) * (1 / (k : ℝ))) atTop (𝓝 b) := by
    have h1 : Tendsto (fun k : ℕ => a / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat a
    have h2 := h1.add (tendsto_const_nhds (x := b) (α := ℕ) (f := atTop))
    rw [zero_add] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkne : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    field_simp
  have hcomp := hcont.comp hexp
  refine hcomp.congr' ?_
  filter_upwards with k
  show Q ^ ((a + b * (k : ℝ)) * (1 / (k : ℝ))) = (Q ^ (a + b * (k : ℝ))) ^ (1 / (k : ℝ))
  rw [Real.rpow_mul hQ.le]

/-- **The archimedean factor of the degree-`d` shift lattice has `k`-th root the cusp constant.** -/
theorem SelbergGammaData.tendsto_norm_asymmetricH_shift_rpow_inv (G : SelbergGammaData)
    (hd : 0 < G.degree) (s₀ : ℂ) :
    Tendsto (fun k : ℕ =>
        (‖G.asymmetricH (s₀ - (k : ℂ) / (G.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop (𝓝 (G.conductor ^ (1 / G.degree) / (2 * Real.pi * G.degree))) := by
  have hpi : (0 : ℝ) < ((2 * Real.pi) ^ G.rank)⁻¹ := by positivity
  have hA : Tendsto (fun k : ℕ => (((2 * Real.pi) ^ G.rank : ℝ)⁻¹) ^ (1 / (k : ℝ))) atTop (𝓝 1) :=
    (tendsto_const_rpow_inv hpi).comp tendsto_natCast_atTop_atTop
  have hQ : Tendsto (fun k : ℕ =>
      (G.Q ^ ((1 - 2 * s₀.re) + 2 / G.degree * (k : ℝ))) ^ (1 / (k : ℝ))) atTop
      (𝓝 (G.Q ^ (2 / G.degree))) := tendsto_rpow_linear_rpow_inv G.Q_pos
  have hG : Tendsto (fun k : ℕ =>
      ((∏ i, ‖Complex.Gamma (((G.pairRate i * (k : ℝ) : ℝ) : ℂ) + G.pairShift s₀ i)‖)
        / (k.factorial : ℝ)) ^ (1 / (k : ℝ))) atTop
      (𝓝 (∏ i, (G.pairRate i) ^ (G.pairRate i))) :=
    tendsto_prod_norm_Gamma_div_factorial_rpow_inv (G.pairRate_pos hd) (G.sum_pairRate hd) _
  have hlim := (hA.mul hQ).mul hG
  rw [one_mul, G.archimedeanRootConstant_eq hd] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hprod : (0 : ℝ) ≤ ∏ i, ‖Complex.Gamma (((G.pairRate i * (k : ℝ) : ℝ) : ℂ)
      + G.pairShift s₀ i)‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hQpow : (0 : ℝ) ≤ G.Q ^ ((1 - 2 * s₀.re) + 2 / G.degree * (k : ℝ)) :=
    (Real.rpow_pos_of_pos G.Q_pos _).le
  rw [G.norm_asymmetricH_shift hd s₀ k]
  rw [show ((2 * Real.pi) ^ G.rank : ℝ)⁻¹
        * G.Q ^ ((1 - 2 * s₀.re) + 2 / G.degree * (k : ℝ))
        * (∏ i, ‖Complex.Gamma (((G.pairRate i * (k : ℝ) : ℝ) : ℂ) + G.pairShift s₀ i)‖)
        / (k.factorial : ℝ)
      = ((2 * Real.pi) ^ G.rank : ℝ)⁻¹
        * (G.Q ^ ((1 - 2 * s₀.re) + 2 / G.degree * (k : ℝ))
          * ((∏ i, ‖Complex.Gamma (((G.pairRate i * (k : ℝ) : ℝ) : ℂ) + G.pairShift s₀ i)‖)
            / (k.factorial : ℝ))) by ring]
  rw [Real.mul_rpow hpi.le (by positivity), Real.mul_rpow hQpow (by positivity), mul_assoc]

end

end RHTower
