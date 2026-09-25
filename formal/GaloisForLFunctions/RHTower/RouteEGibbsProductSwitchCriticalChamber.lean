import GaloisForLFunctions.RHTower.RouteEGibbsProductSwitchCrossing

/-!
# Two curvature chambers of the one-body Gibbs product switch

The mixed sign flips at `β * product = 1`. The Euler-tilt center is `X = σ / β`,
so its canonical shell is not uniformly subcritical. These finite signs do not
control the Möbius-signed sum across product fibres.
-/

open Set
namespace RHTower

private theorem weightedExp_strictMonoOn
    {c a b : ℝ} (hc : 0 ≤ c) (hcb : c * b < 1) :
    StrictMonoOn (fun t : ℝ => t * Real.exp (-c * t)) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) (by fun_prop)
  intro t ht
  have htb : t ≤ b := (interior_subset ht).2
  have hct : c * t < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left htb hc) hcb
  have he : HasDerivAt (fun y : ℝ => Real.exp (-c * y))
      (-c * Real.exp (-c * t)) t := by
    change HasDerivAt (Real.exp ∘ fun y : ℝ => -c * y) _ t
    apply ((Real.hasDerivAt_exp _).comp t
      ((hasDerivAt_id t).const_mul (-c))).congr_deriv
    simp only [id_eq]
    ring
  have hd : deriv (fun t : ℝ => t * Real.exp (-c * t)) t =
      (1 - c * t) * Real.exp (-c * t) := by
    have h' := (hasDerivAt_id t).mul he
    change HasDerivAt (fun y : ℝ => y * Real.exp (-c * y)) _ t at h'
    rw [h'.deriv]
    simp only [id_eq]
    ring
  rw [hd]
  exact mul_pos (by linarith) (Real.exp_pos _)

private theorem gibbsPairDiff_strictAntiOn
    {g h u v β : ℝ} (hβ : 0 < β) (hg : 0 < g) (hu : 0 < u)
    (huv : u < v) (hsub : β * (h * v) < 1) :
    StrictAntiOn (fun x : ℝ => Real.exp (-β * (x * v)) - Real.exp (-β * (x * u)))
      (Icc g h) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc g h) (by fun_prop)
  intro x hx
  have hxin : x ∈ Icc g h := interior_subset hx
  have hxg : g ≤ x := hxin.1
  have hxh : x ≤ h := hxin.2
  have hxpos : 0 < x := lt_of_lt_of_le hg hxg
  have hβx : 0 ≤ β * x := (mul_pos hβ hxpos).le
  have hβxv : (β * x) * v < 1 := by
    calc
      (β * x) * v = β * (x * v) := by ring
      _ ≤ β * (h * v) := by
        have hvpos : 0 < v := lt_trans hu huv
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hxh hvpos.le) hβ.le
      _ < 1 := hsub
  have hmono := weightedExp_strictMonoOn (a := u) (b := v) hβx hβxv
  have huv' : u * Real.exp (-(β * x) * u) <
      v * Real.exp (-(β * x) * v) :=
    hmono (left_mem_Icc.mpr huv.le) (right_mem_Icc.mpr huv.le) huv
  have he (w : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-β * (y * w)))
      (-β * w * Real.exp (-β * (x * w))) x := by
    change HasDerivAt (Real.exp ∘ fun y : ℝ => -β * (y * w)) _ x
    apply ((Real.hasDerivAt_exp _).comp x
      (((hasDerivAt_id x).mul_const w).const_mul (-β))).congr_deriv
    simp only [id_eq]
    ring
  have hd : deriv (fun x : ℝ => Real.exp (-β * (x * v)) -
        Real.exp (-β * (x * u))) x =
      β * (u * Real.exp (-β * (x * u)) - v * Real.exp (-β * (x * v))) := by
    have h' := (he v).sub (he u)
    change HasDerivAt (fun y : ℝ => Real.exp (-β * (y * v)) -
      Real.exp (-β * (y * u))) _ x at h'
    rw [h'.deriv]
    ring
  rw [hd]
  have he1 : -(β * x) * u = -β * (x * u) := by ring
  have he2 : -(β * x) * v = -β * (x * v) := by ring
  rw [he1, he2] at huv'
  exact mul_neg_of_pos_of_neg hβ (sub_neg.mpr huv')

theorem routeEGibbsProductSwitchDefect_neg_of_subcritical
    {g h u v β : ℝ} (hβ : 0 < β) (hg : 0 < g) (hu : 0 < u)
    (hgh : g < h) (huv : u < v) (hsub : β * (h * v) < 1) :
    routeEGibbsProductSwitchDefect g h u v β < 0 := by
  have hanti := gibbsPairDiff_strictAntiOn hβ hg hu huv hsub
  have hlt := hanti (left_mem_Icc.mpr hgh.le) (right_mem_Icc.mpr hgh.le) hgh
  dsimp at hlt
  unfold routeEGibbsProductSwitchDefect
  linarith

private theorem weightedExp_strictAntiOn
    {c a b : ℝ} (hc : 0 < c) (hca : 1 < c * a) :
    StrictAntiOn (fun t : ℝ => t * Real.exp (-c * t)) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) (by fun_prop)
  intro t ht
  have hat : a ≤ t := (interior_subset ht).1
  have hct : 1 < c * t := lt_of_lt_of_le hca (mul_le_mul_of_nonneg_left hat hc.le)
  have he : HasDerivAt (fun y : ℝ => Real.exp (-c * y))
      (-c * Real.exp (-c * t)) t := by
    change HasDerivAt (Real.exp ∘ fun y : ℝ => -c * y) _ t
    apply ((Real.hasDerivAt_exp _).comp t
      ((hasDerivAt_id t).const_mul (-c))).congr_deriv
    simp only [id_eq]
    ring
  have hd : deriv (fun t : ℝ => t * Real.exp (-c * t)) t =
      (1 - c * t) * Real.exp (-c * t) := by
    have h' := (hasDerivAt_id t).mul he
    change HasDerivAt (fun y : ℝ => y * Real.exp (-c * y)) _ t at h'
    rw [h'.deriv]
    simp only [id_eq]
    ring
  rw [hd]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)

private theorem gibbsPairDiff_strictMonoOn
    {g h u v β : ℝ} (hβ : 0 < β) (hg : 0 < g) (hu : 0 < u)
    (huv : u < v) (hsuper : 1 < β * (g * u)) :
    StrictMonoOn (fun x : ℝ => Real.exp (-β * (x * v)) - Real.exp (-β * (x * u)))
      (Icc g h) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc g h) (by fun_prop)
  intro x hx
  have hxin : x ∈ Icc g h := interior_subset hx
  have hxg : g ≤ x := hxin.1
  have hxpos : 0 < x := lt_of_lt_of_le hg hxg
  have hβx : 0 < β * x := mul_pos hβ hxpos
  have hβxu : 1 < (β * x) * u := by
    calc
      1 < β * (g * u) := hsuper
      _ ≤ β * (x * u) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hxg hu.le) hβ.le
      _ = (β * x) * u := by ring
  have hanti := weightedExp_strictAntiOn (a := u) (b := v) hβx hβxu
  have huv' : v * Real.exp (-(β * x) * v) <
      u * Real.exp (-(β * x) * u) :=
    hanti (left_mem_Icc.mpr huv.le) (right_mem_Icc.mpr huv.le) huv
  have he (w : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-β * (y * w)))
      (-β * w * Real.exp (-β * (x * w))) x := by
    change HasDerivAt (Real.exp ∘ fun y : ℝ => -β * (y * w)) _ x
    apply ((Real.hasDerivAt_exp _).comp x
      (((hasDerivAt_id x).mul_const w).const_mul (-β))).congr_deriv
    simp only [id_eq]
    ring
  have hd : deriv (fun x : ℝ => Real.exp (-β * (x * v)) -
        Real.exp (-β * (x * u))) x =
      β * (u * Real.exp (-β * (x * u)) - v * Real.exp (-β * (x * v))) := by
    have h' := (he v).sub (he u)
    change HasDerivAt (fun y : ℝ => Real.exp (-β * (y * v)) -
      Real.exp (-β * (y * u))) _ x at h'
    rw [h'.deriv]
    ring
  rw [hd]
  have he1 : -(β * x) * u = -β * (x * u) := by ring
  have he2 : -(β * x) * v = -β * (x * v) := by ring
  rw [he1, he2] at huv'
  exact mul_pos hβ (sub_pos.mpr huv')

theorem routeEGibbsProductSwitchDefect_pos_of_supercritical
    {g h u v β : ℝ} (hβ : 0 < β) (hg : 0 < g) (hu : 0 < u)
    (hgh : g < h) (huv : u < v) (hsuper : 1 < β * (g * u)) :
    0 < routeEGibbsProductSwitchDefect g h u v β := by
  have hmono := gibbsPairDiff_strictMonoOn (h := h) hβ hg hu huv hsuper
  have hlt := hmono (left_mem_Icc.mpr hgh.le) (right_mem_Icc.mpr hgh.le) hgh
  dsimp at hlt
  unfold routeEGibbsProductSwitchDefect
  linarith

theorem routeEGibbsProductSwitchDefect_neg_below_curvature_threshold
    {g h u v X σ : ℝ} (hσ : 0 < σ) (hX : 0 < X)
    (hg : 0 < g) (hu : 0 < u) (hgh : g < h) (huv : u < v)
    (hbelow : σ * (h * v) < X) :
    routeEGibbsProductSwitchDefect g h u v (σ / X) < 0 := by
  apply routeEGibbsProductSwitchDefect_neg_of_subcritical
    (div_pos hσ hX) hg hu hgh huv
  simpa only [div_mul_eq_mul_div, div_lt_iff₀ hX, one_mul] using hbelow

theorem routeEGibbsProductSwitchDefect_pos_above_curvature_threshold
    {g h u v X σ : ℝ} (hσ : 0 < σ) (hX : 0 < X)
    (hg : 0 < g) (hu : 0 < u) (hgh : g < h) (huv : u < v)
    (habove : X < σ * (g * u)) :
    0 < routeEGibbsProductSwitchDefect g h u v (σ / X) := by
  apply routeEGibbsProductSwitchDefect_pos_of_supercritical
    (div_pos hσ hX) hg hu hgh huv
  simpa only [div_mul_eq_mul_div, lt_div_iff₀ hX, one_mul] using habove

end RHTower
