import GaloisForLFunctions.RHTower.HeatEnergyBridge
import GaloisForLFunctions.RHTower.HeatQuadraticForm

/-!
# The additive-heat double sum

The heat aperture energy of the boundary Dirichlet germ is the absolutely convergent additive
double sum of the Dirichlet coefficients weighted by the Gaussian of the additive difference.
This is the representation `(2)`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

theorem heatCoeff_neg (x : ℝ) (k : ℤ) : heatCoeff x (-k) = heatCoeff x k := by
  rw [heatCoeff, heatCoeff]
  norm_num

/-- The total Gaussian mass on the additive difference lattice. -/
noncomputable def heatCoeffSum (x : ℝ) : ℝ := ∑' k : ℤ, heatCoeff x k

theorem heatCoeffSum_nonneg (x : ℝ) : 0 ≤ heatCoeffSum x :=
  tsum_nonneg fun k => (heatCoeff_pos x k).le

theorem injective_sub_natCast (n : ℕ) : Function.Injective (fun m : ℕ => (n : ℤ) - (m : ℤ)) := by
  intro a b h
  simp only [sub_right_inj, Nat.cast_inj] at h
  exact h

theorem summable_heatCoeff_sub {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Summable (fun m : ℕ => heatCoeff x ((n : ℤ) - (m : ℤ))) :=
  (summable_heatCoeff hx).comp_injective (injective_sub_natCast n)

theorem tsum_heatCoeff_sub_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∑' m : ℕ, heatCoeff x ((n : ℤ) - (m : ℤ))) ≤ heatCoeffSum x :=
  Summable.tsum_le_tsum_of_inj (fun m : ℕ => (n : ℤ) - (m : ℤ)) (injective_sub_natCast n)
    (fun c _ => (heatCoeff_pos x c).le) (fun _ => le_rfl) (summable_heatCoeff_sub hx n)
    (summable_heatCoeff hx)

/-- The left half of the arithmetic-mean majorant of the double sum. -/
noncomputable def heatLeftMajorant (s : ℂ) (x : ℝ) (p : ℕ × ℕ) : ℝ :=
  ((p.1 : ℝ) + 1) ^ (-2 * s.re) * heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ))

theorem heatLeftMajorant_nonneg (s : ℂ) (x : ℝ) (p : ℕ × ℕ) : 0 ≤ heatLeftMajorant s x p := by
  rw [heatLeftMajorant]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (heatCoeff_pos x _).le

set_option maxHeartbeats 1000000 in
theorem summable_heatLeftMajorant {s : ℂ} (h0 : 1 / 2 < s.re) {x : ℝ} (hx : 0 < x) :
    Summable (heatLeftMajorant s x) := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ heatLeftMajorant s x := fun p => heatLeftMajorant_nonneg s x p
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun n => ?_, ?_⟩
  · refine ((summable_heatCoeff_sub hx n).mul_left (((n : ℝ) + 1) ^ (-2 * s.re))).congr
      fun m => ?_
    rw [heatLeftMajorant]
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun m => heatLeftMajorant_nonneg s x (n, m))
    (fun n => ?_) ((summable_truncMajorant h0).mul_right (heatCoeffSum x))
  have hinner : (∑' m : ℕ, heatLeftMajorant s x (n, m))
      = ((n : ℝ) + 1) ^ (-2 * s.re) * ∑' m : ℕ, heatCoeff x ((n : ℤ) - (m : ℤ)) := by
    simp only [heatLeftMajorant]
    exact tsum_mul_left
  rw [hinner]
  exact mul_le_mul_of_nonneg_left (tsum_heatCoeff_sub_le hx n) (Real.rpow_nonneg (by positivity) _)

/-- The right half of the arithmetic-mean majorant of the double sum. -/
noncomputable def heatRightMajorant (s : ℂ) (x : ℝ) (p : ℕ × ℕ) : ℝ :=
  ((p.2 : ℝ) + 1) ^ (-2 * s.re) * heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ))

theorem heatRightMajorant_nonneg (s : ℂ) (x : ℝ) (p : ℕ × ℕ) : 0 ≤ heatRightMajorant s x p := by
  rw [heatRightMajorant]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (heatCoeff_pos x _).le

theorem summable_heatRightMajorant {s : ℂ} (h0 : 1 / 2 < s.re) {x : ℝ} (hx : 0 < x) :
    Summable (heatRightMajorant s x) := by
  refine (Equiv.prodComm ℕ ℕ).summable_iff.mp ?_
  refine (summable_heatLeftMajorant h0 hx).congr fun p => ?_
  simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap, heatLeftMajorant,
    heatRightMajorant]
  rw [← heatCoeff_neg x ((p.1 : ℤ) - (p.2 : ℤ))]
  congr 2
  ring

/-- The additive-heat pair term: two Dirichlet coefficients against the Gaussian of their
additive difference. -/
noncomputable def heatPairTerm (s : ℂ) (x : ℝ) (p : ℕ × ℕ) : ℂ :=
  (((p.1 : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * (starRingEnd ℂ) ((((p.2 : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
    * ((heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ)) : ℝ) : ℂ)

theorem norm_heatPairTerm (s : ℂ) (x : ℝ) (p : ℕ × ℕ) :
    ‖heatPairTerm s x p‖
      = ((p.1 : ℝ) + 1) ^ (-s.re) * ((p.2 : ℝ) + 1) ^ (-s.re)
        * heatCoeff x ((p.1 : ℤ) - (p.2 : ℤ)) := by
  rw [heatPairTerm, norm_mul, norm_mul, RCLike.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < (p.1 : ℝ) + 1),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < (p.2 : ℝ) + 1),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (heatCoeff_pos x _), Complex.neg_re]

theorem norm_heatPairTerm_le (s : ℂ) (x : ℝ) (p : ℕ × ℕ) :
    ‖heatPairTerm s x p‖ ≤ (heatLeftMajorant s x p + heatRightMajorant s x p) / 2 := by
  have h1 : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
  have hsq1 : (((p.1 : ℝ) + 1) ^ (-s.re)) ^ 2 = ((p.1 : ℝ) + 1) ^ (-2 * s.re) := by
    rw [← Real.rpow_natCast (((p.1 : ℝ) + 1) ^ (-s.re)) 2, ← Real.rpow_mul h1.le]
    congr 1
    push_cast
    ring
  have hsq2 : (((p.2 : ℝ) + 1) ^ (-s.re)) ^ 2 = ((p.2 : ℝ) + 1) ^ (-2 * s.re) := by
    rw [← Real.rpow_natCast (((p.2 : ℝ) + 1) ^ (-s.re)) 2, ← Real.rpow_mul h2.le]
    congr 1
    push_cast
    ring
  rw [norm_heatPairTerm, heatLeftMajorant, heatRightMajorant, ← hsq1, ← hsq2]
  have hc := (heatCoeff_pos x ((p.1 : ℤ) - (p.2 : ℤ))).le
  nlinarith [sq_nonneg (((p.1 : ℝ) + 1) ^ (-s.re) - ((p.2 : ℝ) + 1) ^ (-s.re)), hc]

theorem summable_heatPairTerm {s : ℂ} (h0 : 1 / 2 < s.re) {x : ℝ} (hx : 0 < x) :
    Summable (heatPairTerm s x) := by
  refine Summable.of_norm_bounded ?_ (norm_heatPairTerm_le s x)
  exact (((summable_heatLeftMajorant h0 hx).add (summable_heatRightMajorant h0 hx)).div_const 2)

/-- **The additive-heat double sum `(2)`.** -/
noncomputable def heatDoubleSum (s : ℂ) (x : ℝ) : ℂ := ∑' p : ℕ × ℕ, heatPairTerm s x p

theorem tendsto_square_sum {s : ℂ} (h0 : 1 / 2 < s.re) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => ∑ p ∈ Finset.range N ×ˢ Finset.range N, heatPairTerm s x p) atTop
      (𝓝 (heatDoubleSum s x)) := by
  refine (summable_heatPairTerm h0 hx).hasSum.comp
    (tendsto_atTop_finset_of_monotone ?_ ?_)
  · intro a b hab
    have hr : Finset.range a ⊆ Finset.range b := Finset.range_subset_range.mpr hab
    exact Finset.product_subset_product hr hr
  · intro p
    refine ⟨max p.1 p.2 + 1, ?_⟩
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩

theorem sum_heatPairTerm_eq (s : ℂ) (x : ℝ) (N : ℕ) :
    (∑ p ∈ Finset.range N ×ˢ Finset.range N, heatPairTerm s x p)
      = ∑ n ∈ modeSet N, ∑ m ∈ modeSet N,
          (((n : ℝ) : ℂ) ^ (-s) * (starRingEnd ℂ) (((m : ℝ) : ℂ) ^ (-s)))
            * ((heatCoeff x (n - m) : ℝ) : ℂ) := by
  rw [Finset.sum_product, sum_modeSet]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_modeSet]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb1 : ((((i : ℤ) + 1 : ℤ) : ℝ) : ℂ) = (((i : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hb2 : ((((j : ℤ) + 1 : ℤ) : ℝ) : ℂ) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hk : ((i : ℤ) + 1) - ((j : ℤ) + 1) = (i : ℤ) - (j : ℤ) := by ring
  rw [hb1, hb2, hk, heatPairTerm]

theorem heatMoment_two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero]
  push Not
  exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'⟩

/-- The truncated quadratic form is exactly the truncated additive double sum. -/
theorem heatQuadratic_trunc_eq {s : ℂ} {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ θ in Ioc (-Real.pi) Real.pi,
        heatMultiplier x θ * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ))
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N, heatPairTerm s x p := by
  have hq := integral_heatMultiplier_mul_trigPoly_normSq hx (modeSet N)
    (fun n : ℤ => (((n : ℝ)) : ℂ) ^ (-s))
  simp only [dirichletTrunc]
  rw [hq, ← sum_heatPairTerm_eq]
  field_simp

/-- **The heat aperture energy is the additive-heat double sum.**  This is `(1) = (2)`. -/
theorem heatEnergy_eq_heatDoubleSum {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) {x : ℝ}
    (hx : 0 < x) : heatEnergy s x = heatDoubleSum s x := by
  have hcomm : (∫ θ in Ioc (-Real.pi) Real.pi,
      heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)))
      = ∫ θ in Ioc (-Real.pi) Real.pi,
        (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)) * heatMultiplier x θ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    ring
  have hlim := (tendsto_heatIntegral_trunc h0 h1 hx).const_mul (1 / (2 * (Real.pi : ℂ)))
  rw [hcomm] at hlim
  have hlim' : Tendsto (fun N : ℕ => ∑ p ∈ Finset.range N ×ˢ Finset.range N, heatPairTerm s x p)
      atTop (𝓝 (heatEnergy s x)) := by
    refine hlim.congr fun N => heatQuadratic_trunc_eq hx N
  exact tendsto_nhds_unique hlim' (tendsto_square_sum h0 hx)

/-- The double sum in iterated form. -/
theorem heatDoubleSum_eq_iterated {s : ℂ} (h0 : 1 / 2 < s.re) {x : ℝ} (hx : 0 < x) :
    heatDoubleSum s x
      = ∑' n : ℕ, ∑' m : ℕ, (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
          * (starRingEnd ℂ) ((((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
          * ((heatCoeff x ((n : ℤ) - (m : ℤ)) : ℝ) : ℂ) := by
  refine (summable_heatPairTerm h0 hx).tsum_prod' fun n => ?_
  refine Summable.of_norm_bounded
    ((((summable_heatLeftMajorant h0 hx).add
      (summable_heatRightMajorant h0 hx)).div_const 2).prod_factor n) fun m => ?_
  exact norm_heatPairTerm_le s x (n, m)

end RHTower
