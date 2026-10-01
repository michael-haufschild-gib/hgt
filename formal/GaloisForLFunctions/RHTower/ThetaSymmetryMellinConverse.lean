import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# Hecke's converse step for theta series with an arbitrary kernel

Let `θ(y) = Σ_{n≥1} e_n K(n y)`, where `K` is any kernel with absolutely convergent Mellin
transform on a vertical line and the coefficients grow polynomially.

* If `θ` decays faster than every power at infinity and `θ(1/y) = y θ(y)`, then `θ` also decays
  rapidly at `0`, so its Mellin transform `Λ` is entire, and `Λ(1 - s) = Λ(s)`
  (`differentiable_mellin_of_theta_symm`, `mellin_one_sub_eq_of_theta_symm`).
* On `Re s > A + 1`, `Λ(s) = (Σ e_n n^{-s}) · mellin K s` (`mellin_tsum_kernel`).

For `K = Mellin⁻¹[Γℝ(s)^d]` this is the passage from a Voronoi-type theta relation to a
Dirichlet series whose completion `Γℝ(s)^d E(s)` is entire and symmetric under `s ↦ 1 - s`.
-/

open Complex Filter Topology Set Asymptotics MeasureTheory

namespace RHTower

/-- The theta symmetry transports rapid decay at infinity to rapid decay at zero. -/
theorem rapidDecayRay_of_theta_symm {θ : ℝ → ℂ} (hc : ContinuousOn θ (Ioi 0))
    (hdec : ∀ a : ℝ, θ =O[atTop] fun x : ℝ => x ^ (-a))
    (hsym : ∀ y : ℝ, 0 < y → θ (1 / y) = (y : ℂ) * θ y) : RapidDecayRay θ := by
  refine ⟨hc, hdec, fun b => ?_⟩
  have h1 := (hdec (1 - b)).comp_tendsto tendsto_inv_nhdsGT_zero
  have h2 : (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) =O[𝓝[>] 0] fun x : ℝ => x⁻¹ := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    simp
  have h3 := h2.mul h1
  refine h3.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    have := hsym x⁻¹ (inv_pos.mpr hx')
    rw [one_div, inv_inv] at this
    simp [Function.comp, this]
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    simp only [Function.comp]
    rw [Real.inv_rpow hx'.le, Real.rpow_neg hx'.le, inv_inv, Real.rpow_sub hx', Real.rpow_one,
      Real.rpow_neg hx'.le]
    field_simp

/-- The theta symmetry `θ(1/y) = y θ(y)` gives the functional equation `Λ(1 - s) = Λ(s)` for the
Mellin transform. -/
theorem mellin_one_sub_eq_of_theta_symm {θ : ℝ → ℂ}
    (hsym : ∀ y : ℝ, 0 < y → θ (1 / y) = (y : ℂ) * θ y) (s : ℂ) :
    mellin θ (1 - s) = mellin θ s := by
  have h : mellin θ s = mellin (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ) • θ t⁻¹) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    have := hsym t⁻¹ (inv_pos.mpr ht')
    rw [one_div, inv_inv] at this
    simp only [smul_eq_mul]
    rw [this, Complex.cpow_neg_one]
    push_cast
    ring
  rw [h, mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

/-- A rapidly decaying theta-symmetric function has an entire Mellin transform. -/
theorem differentiable_mellin_of_theta_symm {θ : ℝ → ℂ} (hc : ContinuousOn θ (Ioi 0))
    (hdec : ∀ a : ℝ, θ =O[atTop] fun x : ℝ => x ^ (-a))
    (hsym : ∀ y : ℝ, 0 < y → θ (1 / y) = (y : ℂ) * θ y) : Differentiable ℂ (mellin θ) :=
  differentiable_mellin_of_rapidDecayRay (rapidDecayRay_of_theta_symm hc hdec hsym)

/-- Absolute Mellin convergence from integrability of `t^{σ-1}|K(t)|`. -/
theorem mellinConvergent_of_integrableOn_norm {K : ℝ → ℂ} {s : ℂ} (hK : ContinuousOn K (Ioi 0))
    (hKint : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖K t‖) (Ioi 0)) : MellinConvergent K s := by
  unfold MellinConvergent
  refine hKint.mono' ?_ ?_
  · have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi 0) := fun t ht =>
      (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))).continuousWithinAt
    exact (hc.smul hK).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    simp

/-- Scaling `t ↦ b t` multiplies the weighted integral of `|K|` by `b^{-σ}`. -/
theorem integral_norm_scaled_kernel {K : ℝ → ℂ} {σ b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖K (b * t)‖
      = b ^ (-σ) * ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖K t‖ := by
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => (u / b) ^ (σ - 1) * ‖K u‖) 0 hb
  simp only [mul_zero, smul_eq_mul] at h
  have e1 : ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖K (b * t)‖
      = ∫ t in Ioi (0 : ℝ), (b * t / b) ^ (σ - 1) * ‖K (b * t)‖ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [mul_div_cancel_left₀ t hb.ne']
  have e2 : ∫ u in Ioi (0 : ℝ), (u / b) ^ (σ - 1) * ‖K u‖
      = b ^ (1 - σ) * ∫ u in Ioi (0 : ℝ), u ^ (σ - 1) * ‖K u‖ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have hu' : (0 : ℝ) < u := hu
    rw [Real.div_rpow hu'.le hb.le, Real.rpow_sub hb, Real.rpow_one, Real.rpow_sub hb,
      Real.rpow_one]
    field_simp
  rw [e1, h, e2, ← mul_assoc]
  congr 1
  rw [show -σ = (1 - σ) + (-1) by ring, Real.rpow_add hb, Real.rpow_neg_one]
  ring

/-- Termwise Mellin transform of `Σ e_n K(n y)`: the Dirichlet series times `mellin K`. -/
theorem mellin_tsum_kernel {K : ℝ → ℂ} {e : ℕ → ℂ} {A C : ℝ} {s : ℂ}
    (hK : ContinuousOn K (Ioi 0))
    (hKint : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖K t‖) (Ioi 0))
    (he : ∀ n : ℕ, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ A) (hs : A + 1 < s.re) :
    mellin (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) s
      = (∑' n : ℕ, e n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * mellin K s := by
  set σ := s.re with hσ
  set I := ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * ‖K t‖ with hI
  have hb : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hKm : MellinConvergent K s := mellinConvergent_of_integrableOn_norm hK hKint
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) • (e n * K (((n : ℝ) + 1) * t)))
      (volume.restrict (Ioi 0)) := by
    intro n
    have := ((MellinConvergent.comp_mul_left (hb n)).mpr hKm).const_smul (e n)
    simpa [MellinConvergent, smul_eq_mul, IntegrableOn] using this
  have hnorm : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • (e n * K (((n : ℝ) + 1) * t))‖
      = ‖e n‖ * (((n : ℝ) + 1) ^ (-σ) * I) := by
    intro n
    rw [← integral_norm_scaled_kernel (K := K) (σ := σ) (hb n), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [norm_smul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht']
    simp only [sub_re, one_re]
    ring
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi (fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    positivity)
  have hsum : Summable fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • (e n * K (((n : ℝ) + 1) * t))‖ := by
    simp_rw [hnorm]
    have hgeo : Summable fun n : ℕ => C * I * ((n : ℝ) + 1) ^ (A - σ) := by
      apply Summable.mul_left
      have := (Real.summable_nat_rpow (p := A - σ)).mpr (by linarith)
      exact (summable_nat_add_iff 1).mpr this |>.congr (fun n => by push_cast; ring_nf)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
    calc ‖e n‖ * (((n : ℝ) + 1) ^ (-σ) * I) ≤ C * ((n : ℝ) + 1) ^ A * (((n : ℝ) + 1) ^ (-σ) * I) := by
          gcongr; exact he n
      _ = C * I * ((n : ℝ) + 1) ^ (A - σ) := by
          rw [Real.rpow_sub (hb n), Real.rpow_neg (hb n).le]; ring
  unfold mellin
  have hpt : (fun t : ℝ => (t : ℂ) ^ (s - 1) • ∑' n : ℕ, e n * K (((n : ℝ) + 1) * t))
      = fun t : ℝ => ∑' n : ℕ, (t : ℂ) ^ (s - 1) • (e n * K (((n : ℝ) + 1) * t)) := by
    ext t; simp only [smul_eq_mul]; rw [tsum_mul_left]
  rw [hpt, ← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_right]
  congr 1
  ext n
  have hm := mellin_comp_mul_left K s (hb n)
  unfold mellin at hm
  rw [smul_eq_mul] at hm
  calc ∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • (e n * K (((n : ℝ) + 1) * t))
      = e n * ∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • K (((n : ℝ) + 1) * t) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        simp only [smul_eq_mul]; ring
    _ = _ := by rw [hm]; ring

/-- **Hecke's converse step for an arbitrary kernel.** Let `θ(y) = Σ_{n≥1} e_n K(n y)` with
polynomially bounded coefficients, rapid decay at infinity and the theta symmetry
`θ(1/y) = y θ(y)`. Then `Λ = mellin θ` is entire, `Λ(1 - s) = Λ(s)`, and on `Re s > A + 1`
it equals `(Σ e_n n^{-s}) · mellin K s`. -/
theorem hecke_theta_converse {K : ℝ → ℂ} {e : ℕ → ℂ} {A C : ℝ}
    (hK : ContinuousOn K (Ioi 0))
    (he : ∀ n : ℕ, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    (hθc : ContinuousOn (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) (Ioi 0))
    (hθdec : ∀ a : ℝ, (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) =O[atTop]
      fun x : ℝ => x ^ (-a))
    (hθsym : ∀ y : ℝ, 0 < y → (∑' n : ℕ, e n * K (((n : ℝ) + 1) * (1 / y)))
      = (y : ℂ) * ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) :
    Differentiable ℂ (mellin fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) ∧
    (∀ s : ℂ, mellin (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) (1 - s)
      = mellin (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) s) ∧
    (∀ s : ℂ, A + 1 < s.re → IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖K t‖) (Ioi 0) →
      mellin (fun y : ℝ => ∑' n : ℕ, e n * K (((n : ℝ) + 1) * y)) s
        = (∑' n : ℕ, e n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * mellin K s) :=
  ⟨differentiable_mellin_of_theta_symm hθc hθdec hθsym,
    mellin_one_sub_eq_of_theta_symm hθsym,
    fun _ hs hKint => mellin_tsum_kernel hK hKint he hs⟩

end RHTower
