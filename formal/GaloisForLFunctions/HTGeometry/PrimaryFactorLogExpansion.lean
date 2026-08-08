import GaloisForLFunctions.HTGeometry.GeneralPrimaryFactor

/-!
# The exact logarithm of a primary factor, and sharpness of the genus threshold

Inside the unit disc the genus-`g` primary factor is the exponential of the tail of the logarithm
series that its polynomial exponent fails to cancel:

`E_g(z) = exp(-∑_{m ≥ g+1} z^m / m)`.

The tail starts at `g+1`, so `E_g(z) - 1` vanishes to exact order `g+1` at the origin.  Along the
positive reals that gives a matching lower bound `‖E_g(t) - 1‖ ≥ t^{g+1} / (2(g+1))`, which turns
normal convergence of a canonical product on a disc into `(g+1)`-summability of the weights.  The
convergence threshold is therefore necessary, not merely sufficient.
-/

namespace HTGeometry

open scoped BigOperators

/-- The uncancelled tail of the logarithm series: the regularized free energy of one primary
factor. -/
noncomputable def primaryLogTail (g : ℕ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, z ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)

theorem summable_logSeries {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ n / (n : ℂ)) :=
  (Complex.hasSum_taylorSeries_neg_log hz).summable

theorem summable_primaryLogTail (g : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun m : ℕ => z ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)) :=
  (summable_nat_add_iff (f := fun n : ℕ => z ^ n / (n : ℂ)) (g + 1)).2 (summable_logSeries hz)

/-- The polynomial exponent is the head of the logarithm series. -/
theorem primaryExponent_eq_sum_range (g : ℕ) (z : ℂ) :
    primaryExponent g z = ∑ i ∈ Finset.range (g + 1), z ^ i / (i : ℂ) := by
  rw [Finset.sum_range_succ']
  simp [primaryExponent]

/-- **The exact primary-factor logarithm.**  Inside the unit disc the genus-`g` primary factor is
the exponential of the negative uncancelled logarithm tail. -/
theorem primaryFactor_eq_exp_neg_primaryLogTail (g : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    primaryFactor g z = Complex.exp (-primaryLogTail g z) := by
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz' : z = 1 := by linear_combination -h
    rw [hz'] at hz
    simp at hz
  have hlog := Complex.hasSum_taylorSeries_neg_log hz
  have hsplit := (summable_logSeries hz).sum_add_tsum_nat_add (g + 1)
  have hhead : ∑ i ∈ Finset.range (g + 1), z ^ i / (i : ℂ) = primaryExponent g z :=
    (primaryExponent_eq_sum_range g z).symm
  have hkey : primaryExponent g z + primaryLogTail g z = -Complex.log (1 - z) := by
    rw [← hlog.tsum_eq, ← hsplit, hhead]
    rfl
  rw [primaryFactor, ← Complex.exp_log hz1, ← Complex.exp_add]
  congr 1
  linear_combination hkey

/-! ## The primary factor along the positive reals -/

/-- Real form of the uncancelled logarithm tail. -/
noncomputable def realLogTail (g : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℝ)

theorem summable_realLogTail (g : ℕ) {t : ℝ} (ht : |t| < 1) :
    Summable (fun m : ℕ => t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℝ)) := by
  have hgeom : Summable (fun m : ℕ => |t| ^ (g + 1) / ((g : ℝ) + 1) * |t| ^ m) :=
    (summable_geometric_of_lt_one (abs_nonneg t) ht).mul_left _
  refine Summable.of_norm_bounded hgeom fun m => ?_
  have hd : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have hcast : ((m + (g + 1) : ℕ) : ℝ) = (m : ℝ) + ((g : ℝ) + 1) := by push_cast; ring
  have hge : (g : ℝ) + 1 ≤ ((m + (g + 1) : ℕ) : ℝ) := by
    rw [hcast]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hnum : ‖t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℝ)‖
      = |t| ^ (g + 1) * |t| ^ m / ((m + (g + 1) : ℕ) : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((m + (g+1) : ℕ) : ℝ))]
    rw [pow_add, mul_comm (|t| ^ m)]
  rw [hnum]
  have hnn : (0 : ℝ) ≤ |t| ^ (g + 1) * |t| ^ m := by positivity
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < ((m + (g + 1) : ℕ) : ℝ))]
  have : |t| ^ (g + 1) / ((g : ℝ) + 1) * |t| ^ m * ((g : ℝ) + 1)
      = |t| ^ (g + 1) * |t| ^ m := by
    field_simp
  nlinarith [hnn, hge, hd]

theorem realLogTail_nonneg (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ realLogTail g t := by
  refine tsum_nonneg fun m => ?_
  positivity

/-- The tail dominates its leading term. -/
theorem pow_div_le_realLogTail (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t ^ (g + 1) / ((g : ℝ) + 1) ≤ realLogTail g t := by
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hsum := summable_realLogTail g habs
  have hle := hsum.le_tsum 0 (fun m _ => by positivity)
  have hzero : t ^ (0 + (g + 1)) / ((0 + (g + 1) : ℕ) : ℝ) = t ^ (g + 1) / ((g : ℝ) + 1) := by
    norm_num
  rwa [hzero] at hle

/-- The tail is at most twice its leading term on the left half of the unit interval, hence at
most one. -/
theorem realLogTail_le_one (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    realLogTail g t ≤ 1 := by
  have htlt : t < 1 := by linarith
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hsum := summable_realLogTail g habs
  have hgeom : Summable (fun m : ℕ => t * t ^ m) :=
    (summable_geometric_of_lt_one ht0 htlt).mul_left _
  have hbound : ∀ m : ℕ, t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℝ) ≤ t * t ^ m := by
    intro m
    have hd : (1 : ℝ) ≤ ((m + (g + 1) : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ m + (g + 1) := by omega
      exact_mod_cast this
    have hpow : t ^ (m + (g + 1)) ≤ t * t ^ m := by
      have hmono : t ^ (m + (g + 1)) ≤ t ^ (m + 1) :=
        pow_le_pow_of_le_one ht0 (le_of_lt htlt) (by omega)
      calc t ^ (m + (g + 1)) ≤ t ^ (m + 1) := hmono
        _ = t * t ^ m := by rw [pow_succ]; ring
    have hnn : (0 : ℝ) ≤ t ^ (m + (g + 1)) := by positivity
    calc t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℝ) ≤ t ^ (m + (g + 1)) / 1 := by
          refine div_le_div_of_nonneg_left hnn (by norm_num) hd
      _ = t ^ (m + (g + 1)) := by ring
      _ ≤ t * t ^ m := hpow
  have hcmp := Summable.tsum_le_tsum hbound hsum hgeom
  have hval : ∑' m : ℕ, t * t ^ m = t * (1 - t)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one ht0 htlt]
  rw [hval] at hcmp
  have h2 : t * (1 - t)⁻¹ ≤ 1 := by
    have hpos : (0 : ℝ) < 1 - t := by linarith
    rw [mul_inv_le_iff₀ hpos]
    linarith
  exact le_trans hcmp h2

theorem primaryLogTail_ofReal (g : ℕ) (t : ℝ) :
    primaryLogTail g (t : ℂ) = ((realLogTail g t : ℝ) : ℂ) := by
  rw [primaryLogTail, realLogTail, Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  push_cast
  ring

/-- **Sharp lower bound at the origin.**  Along the positive reals the primary factor separates
from one at exactly the order that the tail begins. -/
theorem primaryFactor_sub_one_norm_ge (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    t ^ (g + 1) / (2 * ((g : ℝ) + 1)) ≤ ‖primaryFactor g (t : ℂ) - 1‖ := by
  have htlt : t < 1 := by linarith
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rwa [Complex.norm_real, Real.norm_eq_abs]
  set S : ℝ := realLogTail g t with hS
  have hS0 : 0 ≤ S := realLogTail_nonneg g ht0
  have hS1 : S ≤ 1 := realLogTail_le_one g ht0 ht1
  have hSlow : t ^ (g + 1) / ((g : ℝ) + 1) ≤ S := pow_div_le_realLogTail g ht0 htlt
  have hval : primaryFactor g (t : ℂ) = ((Real.exp (-S) : ℝ) : ℂ) := by
    rw [primaryFactor_eq_exp_neg_primaryLogTail g hnorm, primaryLogTail_ofReal g t, ← hS]
    rw [← Complex.ofReal_neg, Complex.ofReal_exp]
  have hexp : Real.exp (-S) ≤ 1 / (1 + S) := by
    have h1 : S + 1 ≤ Real.exp S := Real.add_one_le_exp S
    have h2 : (0 : ℝ) < 1 + S := by linarith
    have h3 : 1 / Real.exp S ≤ 1 / (1 + S) :=
      one_div_le_one_div_of_le h2 (by linarith)
    rwa [Real.exp_neg, ← one_div]
  have hlow : S / 2 ≤ 1 - Real.exp (-S) := by
    have h2 : (0 : ℝ) < 1 + S := by linarith
    have h3 : 1 - 1 / (1 + S) = S / (1 + S) := by
      field_simp
      ring
    have h4 : S / (1 + S) ≤ 1 - Real.exp (-S) := by
      have := hexp
      linarith [h3]
    have h5 : S / 2 ≤ S / (1 + S) := by
      rw [div_le_div_iff₀ (by norm_num) h2]
      nlinarith
    linarith
  have hle1 : Real.exp (-S) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hnormval : ‖primaryFactor g (t : ℂ) - 1‖ = 1 - Real.exp (-S) := by
    rw [hval]
    rw [show ((Real.exp (-S) : ℝ) : ℂ) - 1 = ((Real.exp (-S) - 1 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  rw [hnormval]
  have hd : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have hsplit2 : t ^ (g + 1) / (2 * ((g : ℝ) + 1)) = (t ^ (g + 1) / ((g : ℝ) + 1)) / 2 := by
    field_simp
  rw [hsplit2]
  linarith [hSlow, hlow]


/-! ## Necessity of the genus threshold -/

/-- **Sharpness of the convergence threshold.**  If the centred genus-`g` primary factors of a
weight family admit a summable majorant uniform on a disc of positive radius, then the weights are
`(g+1)`-summable.  Normal convergence of the canonical product on any disc therefore *forces* the
genus, rather than merely being implied by it. -/
theorem summable_pow_of_normal_majorant {ι : Type*} (g : ℕ) (w : ι → ℂ)
    {R : ℝ} (hR : 0 < R) (M : ι → ℝ)
    (hM : ∀ a, ∀ x : ℂ, ‖x‖ ≤ R → ‖primaryFactor g (x * w a) - 1‖ ≤ M a)
    (hMsum : Summable M) :
    Summable (fun a => ‖w a‖ ^ (g + 1)) := by
  classical
  set D : ℝ := (g : ℝ) + 1 with hD
  have hDpos : (0 : ℝ) < D := by rw [hD]; positivity
  have hRd : (0 : ℝ) < R ^ (g + 1) := by positivity
  have hM0 : ∀ a, 0 ≤ M a := by
    intro a
    have h := hM a 0 (by simpa using le_of_lt hR)
    simpa using h
  -- the sharp pointwise estimate at the truncated radius
  have hkey : ∀ a, (min (R * ‖w a‖) (1 / 2)) ^ (g + 1) / (2 * D) ≤ M a := by
    intro a
    set t : ℝ := min (R * ‖w a‖) (1 / 2) with ht
    have ht0 : 0 ≤ t := le_min (by positivity) (by norm_num)
    have ht2 : t ≤ 1 / 2 := min_le_right _ _
    have htR : t ≤ R * ‖w a‖ := min_le_left _ _
    have hxa : ‖((t : ℂ) / w a)‖ ≤ R := by
      by_cases hwa : w a = 0
      · simp [hwa, le_of_lt hR]
      · have hwpos : (0 : ℝ) < ‖w a‖ := norm_pos_iff.mpr hwa
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0,
          div_le_iff₀ hwpos]
        linarith [htR]
    have hprod : ((t : ℂ) / w a) * w a = (t : ℂ) := by
      by_cases hwa : w a = 0
      · have htz : t = 0 := by
          rw [ht, hwa]
          simp
        simp [hwa, htz]
      · exact div_mul_cancel₀ _ hwa
    have hb := hM a ((t : ℂ) / w a) hxa
    rw [hprod] at hb
    exact le_trans (primaryFactor_sub_one_norm_ge g ht0 ht2) hb
  -- outside a finite set the truncation is inactive
  set c : ℝ := (1 / 2 : ℝ) ^ (g + 1) / (2 * D) with hc
  have hcpos : (0 : ℝ) < c := by rw [hc]; positivity
  have hfin : {a | c ≤ M a}.Finite := by
    have h := hMsum.tendsto_cofinite_zero
    have h2 : ∀ᶠ a in Filter.cofinite, M a ∈ Metric.ball (0 : ℝ) c :=
      h (Metric.ball_mem_nhds 0 hcpos)
    refine (Filter.eventually_cofinite.mp h2).subset ?_
    intro a ha
    simp only [Set.mem_setOf_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt] at ha ⊢
    exact le_trans ha (le_abs_self _)
  set F : Finset ι := hfin.toFinset with hF
  have hout : ∀ a, a ∉ F → ‖w a‖ ^ (g + 1) ≤ (2 * D / R ^ (g + 1)) * M a := by
    intro a haF
    have hlt : M a < c := by
      by_contra hcon
      exact haF (by simp [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt.mp hcon])
    have hmin : min (R * ‖w a‖) (1 / 2) = R * ‖w a‖ := by
      by_contra hcon
      have h12 : min (R * ‖w a‖) (1 / 2) = 1 / 2 := by
        rcases min_cases (R * ‖w a‖) (1 / 2 : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h hcon
        · exact h
      have := hkey a
      rw [h12] at this
      rw [hc] at hlt
      linarith
    have hest := hkey a
    rw [hmin, mul_pow] at hest
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * D)] at hest
    rw [div_mul_eq_mul_div, le_div_iff₀ hRd]
    nlinarith [hest]
  have hmaj : Summable (fun a : ι =>
      (if a ∈ F then ‖w a‖ ^ (g + 1) else 0) + (2 * D / R ^ (g + 1)) * M a) := by
    refine Summable.add ?_ (hMsum.mul_left _)
    exact summable_of_ne_finset_zero (s := F) fun a ha => by simp [ha]
  refine Summable.of_nonneg_of_le
    (fun a => pow_nonneg (norm_nonneg (w a)) (g + 1)) ?_ hmaj
  intro a
  by_cases haF : a ∈ F
  · have hMa : (0 : ℝ) ≤ (2 * D / R ^ (g + 1)) * M a :=
      mul_nonneg (by positivity) (hM0 a)
    simp only [haF, if_true]
    linarith
  · simpa [haF] using hout a haF

end HTGeometry
