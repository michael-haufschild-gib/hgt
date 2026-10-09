import GaloisForLFunctions.RHTower.MobiusRieszSmoothingThreshold

/-!
# Quantitative extinction of normalized threshold packets at fixed scale

Dividing the positive threshold primitive by the product of its shifts gives an
exact box-average recursion. An exponential envelope retains each shift; a
uniform positive lower bound on shifts yields geometric suppression in packet
size and uniform convergence to zero for all logarithmic scales below any fixed cutoff.
-/

noncomputable section

namespace RHTower.MobiusRieszSmoothing

open MeasureTheory Set Filter Topology

/-- Product of the positive logarithmic shifts. -/
def shiftMass (A : List ℝ) : ℝ := A.prod

/-- Threshold primitive normalized by the product of its shifts. -/
def normalizedThreshold (A : List ℝ) (t : ℝ) : ℝ :=
  smoothed A (A.length - 1) t / shiftMass A

theorem shiftMass_pos {A : List ℝ} (hA : ∀ a ∈ A, 0 < a) :
    0 < shiftMass A := by
  induction A with
  | nil => simp [shiftMass]
  | cons a A ih =>
      have ha := hA a (by simp)
      have hA' : ∀ b ∈ A, 0 < b := fun b hb => hA b (by simp [hb])
      simpa [shiftMass] using mul_pos ha (ih hA')

theorem normalizedThreshold_nonneg {A : List ℝ}
    (hA : ∀ a ∈ A, 0 < a) (hne : A ≠ []) (t : ℝ) :
    0 ≤ normalizedThreshold A t := by
  exact div_nonneg (threshold_nonneg A (fun a ha => (hA a ha).le) hne t)
    (shiftMass_pos hA).le

theorem continuous_normalizedThreshold (A : List ℝ) :
    Continuous (normalizedThreshold A) := by
  exact (continuous_smoothed A (A.length - 1)).div_const (shiftMass A)

theorem causal_normalizedThreshold {A : List ℝ}
    (hA : ∀ a ∈ A, 0 ≤ a) : Causal (normalizedThreshold A) := by
  intro t ht
  simp only [normalizedThreshold, causal_smoothed hA (A.length - 1) t ht, zero_div]

theorem normalizedThreshold_cons {A : List ℝ}
    (hA : ∀ b ∈ A, 0 < b) (hne : A ≠ []) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    normalizedThreshold (a :: A) t =
      (∫ u in (t-a)..t, normalizedThreshold A u) / a := by
  have hlen : (a :: A).length - 1 = (A.length - 1) + 1 := by
    have := List.length_pos_iff_ne_nil.mpr hne
    simp only [List.length_cons]
    omega
  rw [normalizedThreshold, hlen,
    smoothed_cons_succ (fun b hb => (hA b hb).le) ha.le,
    shiftMass, List.prod_cons]
  simp only [normalizedThreshold, shiftMass, intervalIntegral.integral_div]
  ring

private theorem hinge_le_one (t : ℝ) : hinge t ≤ 1 := by
  unfold hinge
  exact max_le (by linarith [Real.exp_pos (-t)]) zero_le_one

private theorem normalizedThreshold_single_le {a rate : ℝ}
    (ha : 0 < a) (hrate : 0 < rate) (t : ℝ) :
    normalizedThreshold [a] t ≤ (1 / a) * Real.exp (rate * t) := by
  by_cases ht : t ≤ 0
  · rw [causal_normalizedThreshold (A := [a]) (by simp; exact ha.le) t ht]
    positivity
  · have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
    have hh : hinge t - hinge (t - a) ≤ 1 := by
      have hn : 0 ≤ hinge (t - a) := le_max_right _ _
      linarith [hinge_le_one t]
    have he : 1 ≤ Real.exp (rate * t) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hrate.le ht0)
    simp only [normalizedThreshold, smoothed, packet, shiftMass,
      List.length_cons, List.length_nil, List.prod_cons, List.prod_nil, mul_one,
      Nat.zero_add]
    calc
      _ ≤ 1 / a := div_le_div_of_nonneg_right hh ha.le
      _ ≤ (1 / a) * Real.exp (rate * t) :=
        le_mul_of_one_le_right (by positivity) he

private theorem integral_exp_scale_le {rate : ℝ} (hrate : 0 < rate) (a t : ℝ) :
    (∫ u in (t-a)..t, Real.exp (rate*u)) ≤ Real.exp (rate*t) / rate := by
  have hd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Real.exp (rate*v) / rate)
      (Real.exp (rate*u)) u := by
    intro u
    simpa [hrate.ne'] using! (((hasDerivAt_id u).const_mul rate).exp.div_const rate)
  have hi : IntervalIntegrable (fun u : ℝ => Real.exp (rate*u)) volume (t-a) t :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (rate*u))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi]
  exact sub_le_self _ (by positivity)

/-- An exponential envelope retaining every individual shift in its coefficient. -/
theorem normalizedThreshold_exp_bound {A : List ℝ}
    (hA : ∀ a ∈ A, 0 < a) (hne : A ≠ []) {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    normalizedThreshold A t ≤
      (rate * (A.map (fun a => 1 / (rate*a))).prod) * Real.exp (rate*t) := by
  induction A generalizing t with
  | nil => exact (hne rfl).elim
  | cons a A ih =>
      have ha : 0 < a := hA a (by simp)
      have hA' : ∀ b ∈ A, 0 < b := fun b hb => hA b (by simp [hb])
      rcases eq_or_ne A [] with rfl | hne'
      · have h := normalizedThreshold_single_le ha hrate t
        convert h using 1
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        field_simp
      · rw [normalizedThreshold_cons hA' hne' ha]
        let C := rate * (A.map (fun b => 1 / (rate*b))).prod
        have hC : 0 ≤ C := by
          apply mul_nonneg hrate.le
          apply List.prod_nonneg
          intro b hb
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
          exact (div_pos zero_lt_one (mul_pos hrate (hA' x hx))).le
        have hi : (∫ u in (t-a)..t, normalizedThreshold A u) ≤
            C * Real.exp (rate*t) / rate := by
          calc
            _ ≤ ∫ u in (t-a)..t, C * Real.exp (rate*u) :=
              intervalIntegral.integral_mono_on (by linarith)
                ((continuous_normalizedThreshold A).intervalIntegrable _ _)
                ((by fun_prop : Continuous (fun u : ℝ => C * Real.exp (rate*u))).intervalIntegrable _ _)
                (fun u _ => ih hA' hne' u)
            _ = C * ∫ u in (t-a)..t, Real.exp (rate*u) :=
              intervalIntegral.integral_const_mul _ _
            _ ≤ C * (Real.exp (rate*t) / rate) :=
              mul_le_mul_of_nonneg_left (integral_exp_scale_le hrate a t) hC
            _ = _ := by ring
        calc
          _ ≤ (C * Real.exp (rate*t) / rate) / a := div_le_div_of_nonneg_right hi ha.le
          _ = _ := by
            simp only [List.map_cons, List.prod_cons]
            dsimp [C]
            field_simp

/-- Uniform positive lower bounds for shifts yield geometric suppression in packet size. -/
theorem normalizedThreshold_geometric_bound {A : List ℝ} {c : ℝ}
    (hc : 0 < c) (hA : ∀ a ∈ A, c ≤ a) (hne : A ≠ []) (t : ℝ) :
    normalizedThreshold A t ≤
      ((2 / c) * (1 / 2 : ℝ) ^ A.length) * Real.exp ((2 / c) * t) := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => hc.trans_le (hA a ha)
  have hp : (A.map (fun a => 1 / ((2 / c) * a))).prod ≤ (1 / 2 : ℝ)^A.length := by
    clear hpos hne
    induction A with
    | nil => simp
    | cons a A ih =>
        have ha := hA a (by simp)
        have hA' : ∀ b ∈ A, c ≤ b := fun b hb => hA b (by simp [hb])
        have hpa : 2 ≤ (2 / c) * a := by
          have hh := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2 / c)
          have he : (2 / c) * c = 2 := by field_simp
          rwa [he] at hh
        have hrec : 1 / ((2 / c) * a) ≤ (1 / 2 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) hpa
        simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
        have hpA : 0 ≤ (A.map (fun b => 1 / ((2 / c) * b))).prod := by
          apply List.prod_nonneg
          intro b hb
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
          exact (div_pos zero_lt_one (mul_pos (by positivity) (hc.trans_le (hA' x hx)))).le
        calc
          _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ)^A.length :=
            mul_le_mul hrec (ih hA') hpA (by norm_num)
          _ = _ := by ring
  calc
    _ ≤ ((2/c) * (A.map (fun a => 1 / ((2/c)*a))).prod) * Real.exp ((2/c)*t) :=
      normalizedThreshold_exp_bound hpos hne (by positivity) t
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_pos _).le

/-- The estimate is uniform on the entire half-line below a fixed cutoff. -/
theorem normalizedThreshold_halfline_bound {A : List ℝ} {c T t : ℝ}
    (hc : 0 < c) (hA : ∀ a ∈ A, c ≤ a) (hne : A ≠ []) (ht : t ≤ T) :
    normalizedThreshold A t ≤
      ((2 / c) * Real.exp ((2 / c) * T)) * (1 / 2 : ℝ)^A.length := by
  calc
    _ ≤ ((2/c) * (1/2:ℝ)^A.length) * Real.exp ((2/c)*t) :=
      normalizedThreshold_geometric_bound hc hA hne t
    _ ≤ ((2/c) * (1/2:ℝ)^A.length) * Real.exp ((2/c)*T) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by positivity))) (by positivity)
    _ = _ := by ring

/-- Increasing threshold smoothing extinguishes the normalized packet uniformly at fixed scale. -/
theorem tendstoUniformlyOn_normalizedThreshold {ι : Type*} {l : Filter ι}
    {A : ι → List ℝ} {c : ℝ} (hc : 0 < c)
    (hA : ∀ i, ∀ a ∈ A i, c ≤ a)
    (hlen : Tendsto (fun i => (A i).length) l atTop) (T : ℝ) :
    TendstoUniformlyOn (fun i => normalizedThreshold (A i)) (fun _ => 0) l (Iic T) := by
  let C := (2 / c) * Real.exp ((2 / c) * T)
  have hp : Tendsto (fun i => C * (1/2:ℝ)^(A i).length) l (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).comp hlen
    simpa using hh.const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hp.eventually (gt_mem_nhds hε),
    hlen.eventually (eventually_ge_atTop 1)] with i hi hlen'
  intro t ht
  have hne : A i ≠ [] := by intro h; simp [h] at hlen'
  have hn := normalizedThreshold_nonneg (fun a ha => hc.trans_le (hA i a ha)) hne t
  have hb := normalizedThreshold_halfline_bound hc (hA i) hne ht
  simpa only [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg hn] using lt_of_le_of_lt hb hi

end RHTower.MobiusRieszSmoothing
