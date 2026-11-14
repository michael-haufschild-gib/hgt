import GaloisForLFunctions.HTGeometry.DirichletWirtinger

/-!
# The mass of an even source's centered primitive

Even reflection gives the mixed-boundary constant `4/π²`. Subtracting the
primitive's affine part instead retains its mean and quadratic Legendre
charges, with Dirichlet constant `1/π²` on the remaining variance.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology intervalIntegral
namespace GaloisForLFunctions.LatticeSectionTheory

/-- Reflection at the Neumann endpoint gives the sharp mixed-boundary Wirtinger constant. -/
private theorem mixed_wirtinger {H F : ℝ → ℝ} (hF : Continuous F)
    (hD : ∀ x, HasDerivAt H (F x) x) (hH0 : H 0 = 0) (hF1 : F 1 = 0) :
    (∫ x in (0 : ℝ)..1, H x ^ 2) ≤
      (2 / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..1, F x ^ 2 := by
  let g : ℝ → ℝ := (Iic (1 : ℝ)).piecewise H (fun x => H (2 - x))
  let g' : ℝ → ℝ := (Iic (1 : ℝ)).piecewise F (fun x => -F (2 - x))
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hgc : Continuous g := Continuous.piecewise (by
      intro x hx
      have hx' : x = 1 := by simpa only [frontier_Iic, mem_singleton_iff] using hx
      subst x
      norm_num) hH (hH.comp (continuous_const.sub continuous_id))
  have hgc' : Continuous g' := Continuous.piecewise (by
      intro x hx
      have hx' : x = 1 := by simpa only [frontier_Iic, mem_singleton_iff] using hx
      subst x
      norm_num [hF1]) hF (hF.comp (continuous_const.sub continuous_id)).neg
  have hR (x : ℝ) : HasDerivAt (fun y => H (2 - y)) (-F (2 - x)) x := by
    exact ((hD (2 - x)).scomp x ((hasDerivAt_id x).const_sub 2)).congr_deriv
      (by simp only [smul_eq_mul, neg_one_mul])
  have hgd (x : ℝ) : HasDerivAt g (g' x) x := by
    rcases lt_trichotomy x 1 with hx | hx | hx
    · rw [show g' x = F x by exact piecewise_eq_of_mem _ _ _ (show x ∈ Iic (1 : ℝ) from hx.le)]
      apply (hD x).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hx] with y hy
      change y < (1 : ℝ) at hy
      exact piecewise_eq_of_mem _ _ _ (show y ∈ Iic (1 : ℝ) from hy.le)
    · subst x
      have hL : HasDerivWithinAt g 0 (Iic (1 : ℝ)) 1 := by
        have h := (hD 1).hasDerivWithinAt (s := Iic (1 : ℝ))
        rw [hF1] at h
        exact h.congr (fun y hy => piecewise_eq_of_mem _ _ _ hy)
          (piecewise_eq_of_mem _ _ _ (by simp))
      have hright : HasDerivWithinAt g 0 (Ici (1 : ℝ)) 1 := by
        have h := (hR 1).hasDerivWithinAt (s := Ici (1 : ℝ))
        norm_num [hF1] at h
        refine h.congr (fun y hy => ?_) ?_
        · change (1 : ℝ) ≤ y at hy
          rcases eq_or_lt_of_le hy with hy | hy
          · subst y
            norm_num [g]
          · exact piecewise_eq_of_notMem _ _ _ (not_le.mpr hy)
        · norm_num [g]
      have h := hL.union hright
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
      simpa [g', hF1] using h
    · rw [show g' x = -F (2 - x) by exact piecewise_eq_of_notMem _ _ _ (not_le.mpr hx)]
      apply (hR x).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change (1 : ℝ) < y at hy
      exact piecewise_eq_of_notMem _ _ _ (not_le.mpr hy)
  have h := HTGeometry.dirichlet_wirtinger_intervalIntegral
    (a := (0 : ℝ)) (b := 2) (by norm_num)
    (f := fun x => (g x : ℂ)) (f' := fun x => (g' x : ℂ))
    (fun x _ => (hgd x).ofReal_comp)
    (Complex.continuous_ofReal.comp hgc').continuousOn
    (by simp [g, hH0]) (by norm_num [g, hH0])
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have hleft (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) : x ≤ 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact hx.2
  have hright (x : ℝ) (hx : x ∈ uIcc (1 : ℝ) 2) : 1 ≤ x := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    exact hx.1
  have hgR (x : ℝ) (hx : 1 ≤ x) : g x = H (2 - x) := by
    rcases eq_or_lt_of_le hx with hx | hx
    · subst x
      norm_num [g]
    · exact piecewise_eq_of_notMem _ _ _ (not_le.mpr hx)
  have hgR' (x : ℝ) (hx : 1 ≤ x) : g' x = -F (2 - x) := by
    rcases eq_or_lt_of_le hx with hx | hx
    · subst x
      norm_num [g', hF1]
    · exact piecewise_eq_of_notMem _ _ _ (not_le.mpr hx)
  have hmass : (∫ x in (0 : ℝ)..2, g x ^ 2) = 2 * ∫ x in (0 : ℝ)..1, H x ^ 2 := by
    rw [← integral_add_adjacent_intervals (f := fun x => g x ^ 2) (μ := volume) ((hgc.pow 2).intervalIntegrable 0 1)
      ((hgc.pow 2).intervalIntegrable 1 2),
      integral_congr (a := (0 : ℝ)) (b := 1) (g := fun x => H x ^ 2)
        (fun x hx => by dsimp only [g]; rw [piecewise_eq_of_mem (Iic (1 : ℝ)) _ _ (show x ∈ Iic (1 : ℝ) from hleft x hx)]),
      integral_congr (a := (1 : ℝ)) (b := 2) (g := fun x => H (2 - x) ^ 2)
        (fun x hx => by rw [hgR x (hright x hx)]),
      integral_comp_sub_left (f := fun x => H x ^ 2) (a := (1 : ℝ)) (b := 2) (d := 2)]
    norm_num
    ring
  have henergy : (∫ x in (0 : ℝ)..2, g' x ^ 2) = 2 * ∫ x in (0 : ℝ)..1, F x ^ 2 := by
    rw [← integral_add_adjacent_intervals (f := fun x => g' x ^ 2) (μ := volume) ((hgc'.pow 2).intervalIntegrable 0 1)
      ((hgc'.pow 2).intervalIntegrable 1 2),
      integral_congr (a := (0 : ℝ)) (b := 1) (g := fun x => F x ^ 2)
        (fun x hx => by dsimp only [g']; rw [piecewise_eq_of_mem (Iic (1 : ℝ)) _ _ (show x ∈ Iic (1 : ℝ) from hleft x hx)]),
      integral_congr (a := (1 : ℝ)) (b := 2) (g := fun x => F (2 - x) ^ 2)
        (fun x hx => by rw [hgR' x (hright x hx), neg_sq]),
      integral_comp_sub_left (f := fun x => F x ^ 2) (a := (1 : ℝ)) (b := 2) (d := 2)]
    norm_num
    ring
  rw [hmass, henergy] at h
  norm_num only [sub_zero] at h
  linarith only [h]

private theorem even_integral_unit {H : ℝ → ℝ} (hH : Continuous H)
    (he : ∀ x, H (-x) = H x) :
    (∫ x in Icc (-1 : ℝ) 1, H x) = 2 * ∫ x in (0 : ℝ)..1, H x := by
  have hn := intervalIntegral.integral_comp_neg (f := H) (a := (0 : ℝ)) (b := 1)
  simp only [he, neg_zero] at hn
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hH.intervalIntegrable (-1) 0) (hH.intervalIntegrable 0 1)
  rw [← hn, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  linarith only [h]

/-- The centered primitive of an even unit-supported source has the sharp mixed-boundary mass bound. -/
theorem even_centered_primitive_mass_le {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) (heven : ∀ x, F (-x) = F x) :
    (∫ x in Icc (-1 : ℝ) 1, (∫ y in (0 : ℝ)..x, F y) ^ 2) ≤
      (4 / Real.pi ^ 2) * ∫ x, F x ^ 2 := by
  let H : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, F y
  have hD (x : ℝ) : HasDerivAt H (F x) x := (hF.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hH0 : H 0 = 0 := by simp [H]
  have hF1 : F 1 = 0 := by
    have hz : Ioi (1 : ℝ) ⊆ {x | F x = 0} := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport fun ht => not_le_of_gt hx (hs ht).2
    have h := closure_minimal hz (isClosed_eq hF continuous_const)
    rw [closure_Ioi] at h
    exact h (by simp)
  have hHo (x : ℝ) : H (-x) = -H x := by
    have h := intervalIntegral.integral_comp_neg (f := F) (a := (0 : ℝ)) (b := x)
    simp only [heven, neg_zero] at h
    dsimp [H]
    rw [intervalIntegral.integral_symm, ← h]
  have h := mixed_wirtinger hF hD hH0 hF1
  have hHm := even_integral_unit (H := fun x => H x ^ 2)
    (hH.pow 2) (fun x => by rw [hHo, neg_sq])
  have hFm := even_integral_unit (H := fun x => F x ^ 2)
    (hF.pow 2) (fun x => by rw [heven])
  have hcut : (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) = ∫ x, F x ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_pow two_ne_zero]
  rw [hcut] at hFm
  have hc : (2 / Real.pi) ^ 2 = 4 / Real.pi ^ 2 := by ring
  rw [hc] at h
  change (∫ x in Icc (-1 : ℝ) 1, H x ^ 2) ≤ _
  rw [hHm, hFm]
  nlinarith only [h]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.even_centered_primitive_mass_le

namespace GaloisForLFunctions.LatticeSectionTheory

/-- Subtracting the primitive's affine part retains its mean and quadratic Legendre charges. -/
theorem primitive_mass_le_variance_and_two_moments {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..x, G y) ^ 2) ≤
      (1 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..1, G x ^ 2) +
      (1 / 3 - 1 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..1, G x) ^ 2 -
      (2 / 3 : ℝ) * (∫ x in (0 : ℝ)..1, G x) *
        (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2)) := by
  let H : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, G y
  let m := ∫ x in (0 : ℝ)..1, G x
  let m2 := ∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2)
  let J : ℝ → ℝ := fun x => H x - m * x
  have hD (x : ℝ) : HasDerivAt H (G x) x := (hG.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hJ : Continuous J := hH.sub (continuous_const.mul continuous_id)
  have hDJ (x : ℝ) : HasDerivAt J (G x - m) x := by
    exact ((hD x).sub ((hasDerivAt_id x).const_mul m)).congr_deriv (by simp)
  have hw := HTGeometry.dirichlet_wirtinger_intervalIntegral
    (a := (0 : ℝ)) (b := 1) (by norm_num)
    (f := fun x => (J x : ℂ)) (f' := fun x => (G x - m : ℝ))
    (fun x _ => (hDJ x).ofReal_comp)
    (Complex.continuous_ofReal.comp (hG.sub continuous_const)).continuousOn
    (by simp [J, H]) (by simp [J, H, m])
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero] at hw
  have hprod (x : ℝ) : HasDerivAt (fun y => y ^ 2 * H y)
      (2 * (x * H x) + x ^ 2 * G x) x := by
    exact (((hasDerivAt_id x).pow 2).mul (hD x)).congr_deriv (by simp only [id_eq, Pi.pow_apply]; ring)
  have hcprod : Continuous (fun x => 2 * (x * H x) + x ^ 2 * G x) := by fun_prop
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (f := fun x => x ^ 2 * H x) (fun x _ => hprod x) (hcprod.intervalIntegrable 0 1)
  have hiH : IntervalIntegrable (fun x => x * H x) volume 0 1 :=
    (continuous_id.mul hH).intervalIntegrable 0 1
  have hiG : IntervalIntegrable (fun x => x ^ 2 * G x) volume 0 1 :=
    ((continuous_pow 2).mul hG).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (μ := volume)
    (f := fun x => 2 * (x * H x)) (g := fun x => x ^ 2 * G x)
    (hiH.const_mul 2) hiG, intervalIntegral.integral_const_mul] at ht
  change 2 * (∫ x in (0 : ℝ)..1, x * H x) +
    (∫ x in (0 : ℝ)..1, x ^ 2 * G x) = 1 ^ 2 * H 1 - 0 ^ 2 * H 0 at ht
  norm_num only [one_pow, zero_pow, OfNat.ofNat_ne_zero, one_mul, zero_mul, sub_zero] at ht
  change 2 * (∫ x in (0 : ℝ)..1, x * H x) +
    (∫ x in (0 : ℝ)..1, x ^ 2 * G x) = m at ht
  have hm2 : m2 = (3 * (∫ x in (0 : ℝ)..1, x ^ 2 * G x) - m) / 2 := by
    have he : (fun x => G x * ((3 * x ^ 2 - 1) / 2)) =
        fun x => (3 * (x ^ 2 * G x) - G x) / 2 := by funext x; ring
    dsimp only [m2]
    rw [he, intervalIntegral.integral_div, intervalIntegral.integral_sub (μ := volume)
      (f := fun x => 3 * (x ^ 2 * G x)) (g := G)
      (hiG.const_mul 3) (hG.intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul]
  have hJmass : (∫ x in (0 : ℝ)..1, J x ^ 2) =
      (∫ x in (0 : ℝ)..1, H x ^ 2) -
      2 * m * (∫ x in (0 : ℝ)..1, x * H x) + m ^ 2 / 3 := by
    have he : (fun x => J x ^ 2) =
        fun x => H x ^ 2 - 2 * m * (x * H x) + m ^ 2 * x ^ 2 := by
      funext x
      dsimp [J]
      ring
    rw [he, intervalIntegral.integral_add (μ := volume)
        (f := fun x => H x ^ 2 - 2 * m * (x * H x)) (g := fun x => m ^ 2 * x ^ 2)
        ((hH.pow 2).intervalIntegrable 0 1 |>.sub (hiH.const_mul (2 * m)))
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (μ := volume)
        (f := fun x => H x ^ 2) (g := fun x => 2 * m * (x * H x))
        ((hH.pow 2).intervalIntegrable 0 1) (hiH.const_mul (2 * m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hdermass : (∫ x in (0 : ℝ)..1, (G x - m) ^ 2) =
      (∫ x in (0 : ℝ)..1, G x ^ 2) - m ^ 2 := by
    have he : (fun x => (G x - m) ^ 2) = fun x => G x ^ 2 - 2 * m * G x + m ^ 2 := by
      funext x
      ring
    rw [he, intervalIntegral.integral_add (μ := volume)
        (f := fun x => G x ^ 2 - 2 * m * G x) (g := fun _ : ℝ => m ^ 2)
        (((hG.pow 2).intervalIntegrable 0 1).sub
        ((hG.intervalIntegrable 0 1).const_mul (2 * m))) (continuous_const.intervalIntegrable 0 1),
      intervalIntegral.integral_sub (μ := volume)
        (f := fun x => G x ^ 2) (g := fun x => 2 * m * G x)
        ((hG.pow 2).intervalIntegrable 0 1) ((hG.intervalIntegrable 0 1).const_mul (2 * m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    change _ - 2 * m * m + (1 - 0) • m ^ 2 = _
    simp only [sub_zero, one_smul]
    ring
  rw [hJmass, hdermass, show (1 / Real.pi) ^ 2 = 1 / Real.pi ^ 2 by ring] at hw
  change (∫ x in (0 : ℝ)..1, H x ^ 2) ≤
    (1 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..1, G x ^ 2) +
      (1 / 3 - 1 / Real.pi ^ 2) * m ^ 2 - (2 / 3) * m * m2
  have htM := congrArg (fun z => m * z) ht
  have hm2M := congrArg (fun z => m * z) hm2
  nlinarith only [hw, htM, hm2M]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.primitive_mass_le_variance_and_two_moments

namespace GaloisForLFunctions.LatticeSectionTheory

/-- A rational form of the charged primitive bound, rounded only on the mean-zero variance. -/
theorem primitive_mass_le_rational_variance_and_two_moments {G : ℝ → ℝ} (hG : Continuous G) :
    (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..x, G y) ^ 2) ≤
      (5 / 49 : ℝ) * (∫ x in (0 : ℝ)..1, G x ^ 2) +
      (1 / 3 - 5 / 49 : ℝ) * (∫ x in (0 : ℝ)..1, G x) ^ 2 -
      (2 / 3 : ℝ) * (∫ x in (0 : ℝ)..1, G x) *
        (∫ x in (0 : ℝ)..1, G x * ((3 * x ^ 2 - 1) / 2)) := by
  let m := ∫ x in (0 : ℝ)..1, G x
  have hvar : m ^ 2 ≤ ∫ x in (0 : ℝ)..1, G x ^ 2 := by
    have hn : 0 ≤ ∫ x in (0 : ℝ)..1, (G x - m) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg (G x - m))
    have he : (fun x => (G x - m) ^ 2) = fun x => G x ^ 2 - 2 * m * G x + m ^ 2 := by
      funext x
      ring
    rw [he, intervalIntegral.integral_add (μ := volume)
        (f := fun x => G x ^ 2 - 2 * m * G x) (g := fun _ : ℝ => m ^ 2)
        (((hG.pow 2).intervalIntegrable 0 1).sub
        ((hG.intervalIntegrable 0 1).const_mul (2 * m))) (continuous_const.intervalIntegrable 0 1),
      intervalIntegral.integral_sub (μ := volume)
        (f := fun x => G x ^ 2) (g := fun x => 2 * m * G x)
        ((hG.pow 2).intervalIntegrable 0 1) ((hG.intervalIntegrable 0 1).const_mul (2 * m)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
    change 0 ≤ _ - 2 * m * m + (1 - 0) • m ^ 2 at hn
    simp only [sub_zero, one_smul] at hn
    nlinarith only [hn]
  have hc : 1 / Real.pi ^ 2 ≤ (5 / 49 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    have hpi := Real.pi_gt_d2
    nlinarith only [hpi, sq_nonneg (Real.pi - 157 / 50)]
  have hpay := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hvar)
  have h := primitive_mass_le_variance_and_two_moments hG
  dsimp only [m] at hpay
  nlinarith only [h, hpay]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.primitive_mass_le_rational_variance_and_two_moments
