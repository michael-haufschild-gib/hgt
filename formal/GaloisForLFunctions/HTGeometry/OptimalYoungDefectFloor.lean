import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Exact optimization of a Young defect family

For mass M, defect D and reference energy E, combine `E ≥ f M` with every
Young bound `E ≥ (r−x)D−(A/x+R)M`, x>0. Their intersection has defect ceiling
`s²`, where `s=(√A+√(A+r(R+f)))/r`. A perturbation `e(D+M)` leaves the exact
floor `f−e(1+s²)` up to reserve `r−√A/s`, then `−R−e−A/(r−e)` until e=r.
Beyond that reserve the scalar energies are unbounded below. Explicit witnesses
attain both regimes. With R≥0, positivity has exactly the first-regime criterion.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.YoungDefect

/-- Positive root of the quadratic obtained by optimizing the Young family. -/
def scale (r A q : ℝ) : ℝ := (Real.sqrt A + Real.sqrt (A + r * q)) / r

lemma scale_properties {r A q : ℝ} (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ q) :
    0 < scale r A q ∧ r * scale r A q = Real.sqrt A + Real.sqrt (A + r * q) ∧
      r * (scale r A q)^2 - 2 * Real.sqrt A * scale r A q = q := by
  have hu : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hAq : 0 < A + r * q := add_pos_of_pos_of_nonneg hA (mul_nonneg hr.le hq)
  have hv : 0 < Real.sqrt (A + r * q) := Real.sqrt_pos.mpr hAq
  have he : r * scale r A q = Real.sqrt A + Real.sqrt (A + r * q) := by
    unfold scale
    field_simp [hr.ne']
  refine ⟨div_pos (add_pos hu hv) hr, he, ?_⟩
  have hu2 := Real.sq_sqrt hA.le
  have hv2 := Real.sq_sqrt hAq.le
  have he2 := congrArg (fun x : ℝ => x^2) he
  have hue := congrArg (fun x : ℝ => 2 * Real.sqrt A * x) he
  have hm : r * (r * (scale r A q)^2 - 2 * Real.sqrt A * scale r A q) = r * q := by
    nlinarith only [hu2, hv2, he2, hue]
  exact mul_left_cancel₀ hr.ne' hm

/-- Every Young parameter lies above the same explicit defect ceiling. -/
lemma family_bound {r A q : ℝ} (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ q)
    {x : ℝ} (hx : 0 < x) :
    (r - x) * (scale r A q)^2 ≤ A / x + q := by
  obtain ⟨_, _, hrel⟩ := scale_properties hr hA hq
  have hu2 := Real.sq_sqrt hA.le
  have he : A + x * q - x * ((r - x) * (scale r A q)^2) =
      (x * scale r A q - Real.sqrt A)^2 := by
    have hm := congrArg (fun z : ℝ => x * z) hrel
    nlinarith only [hm, hu2]
  apply (mul_le_mul_iff_right₀ hx).mp
  have hsq := sq_nonneg (x * scale r A q - Real.sqrt A)
  calc
    x * ((r - x) * (scale r A q)^2) ≤ A + x * q := by linarith only [he, hsq]
    _ = x * (A / x + q) := by field_simp [hx.ne']

/-- The minimizing Young parameter leaves a strictly positive defect reserve. -/
lemma optimal_parameter_properties {r A q : ℝ} (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ q) :
    0 < Real.sqrt A / scale r A q ∧
      Real.sqrt A / scale r A q < r ∧
      (A / (Real.sqrt A / scale r A q) + q) /
          (r - Real.sqrt A / scale r A q) = (scale r A q)^2 := by
  obtain ⟨hs, he, hrel⟩ := scale_properties hr hA hq
  have hu : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hv : 0 < Real.sqrt (A + r * q) :=
    Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg hA (mul_nonneg hr.le hq))
  let x := Real.sqrt A / scale r A q
  have hx : 0 < x := div_pos hu hs
  have hxs : x * scale r A q = Real.sqrt A := div_mul_cancel₀ _ hs.ne'
  have hxr : x < r := by
    apply (mul_lt_mul_iff_left₀ hs).mp
    rw [hxs, he]
    exact lt_add_of_pos_right _ hv
  refine ⟨hx, hxr, ?_⟩
  apply (div_eq_iff (sub_pos.mpr hxr).ne').mpr
  have hquot : A / x = Real.sqrt A * scale r A q := by
    apply (div_eq_iff hx.ne').mpr
    calc
      A = Real.sqrt A * Real.sqrt A := (Real.mul_self_sqrt hA.le).symm
      _ = Real.sqrt A * scale r A q * x := by rw [← hxs]; ring
  change A / x + q = _
  rw [hquot]
  have heq : (scale r A q)^2 * (r - x) =
      r * (scale r A q)^2 - Real.sqrt A * scale r A q := by
    calc
      _ = r * (scale r A q)^2 - (x * scale r A q) * scale r A q := by ring
      _ = _ := by rw [hxs]
  rw [heq]
  linarith only [hrel]

/-- The optimal reserve parameter is attained inside the positive-reserve interval. -/
lemma family_attained {r A q : ℝ} (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ q) :
    ∃ x : ℝ, 0 < x ∧ x < r ∧
      (A / x + q) / (r - x) = (scale r A q)^2 :=
  ⟨Real.sqrt A / scale r A q, optimal_parameter_properties hr hA hq⟩

/-- The explicit ceiling is the exact minimum over every positive reserve choice. -/
theorem optimal_young_loss {r A q : ℝ} (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ q) :
    (∀ x : ℝ, 0 < x → x < r →
      (scale r A q)^2 ≤ (A / x + q) / (r - x)) ∧
    (∃ x : ℝ, 0 < x ∧ x < r ∧
      (A / x + q) / (r - x) = (scale r A q)^2) := by
  refine ⟨?_, family_attained hr hA hq⟩
  intro x hx hxr
  apply (le_div_iff₀ (sub_pos.mpr hxr)).mpr
  simpa only [mul_comm] using family_bound hr hA hq hx

/-- Convex interpolation spends precisely the reserve needed by the perturbation. -/
lemma floor_of_two_bounds {M D E F f B a e : ℝ} (ha : 0 < a)
    (he : 0 ≤ e) (hea : e ≤ a)
    (hf : f * M ≤ E) (hc : a * D - B * M ≤ E)
    (hp : -e * (D + M) ≤ F - E) :
    (f - e * (1 + (B + f) / a)) * M ≤ F := by
  have h1 := mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr hea)
  have h2 := mul_le_mul_of_nonneg_left hc he
  have h3 := mul_le_mul_of_nonneg_left hp ha.le
  have hcoef : a * (f - e * (1 + (B + f) / a)) =
      (a - e) * f - e * B - a * e := by field_simp [ha.ne']; ring
  apply (mul_le_mul_iff_right₀ ha).mp
  rw [← mul_assoc, hcoef]
  nlinarith only [h1, h2, h3]

/-- The optimum over all center Young parameters and convex weights. -/
theorem floor_of_young_family {r A R f M D E F e : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ R + f)
    (he : 0 ≤ e) (hea : e ≤ r - Real.sqrt A / scale r A (R + f))
    (hf : f * M ≤ E)
    (hc : ∀ x : ℝ, 0 < x → (r - x) * D - (A / x + R) * M ≤ E)
    (hp : -e * (D + M) ≤ F - E) :
    (f - e * (1 + (scale r A (R + f))^2)) * M ≤ F := by
  obtain ⟨hx, hxr, heq⟩ := optimal_parameter_properties hr hA hq
  have h := floor_of_two_bounds (sub_pos.mpr hxr) he hea hf (hc _ hx) hp
  have hsum : (A / (Real.sqrt A / scale r A (R + f)) + R + f) /
      (r - Real.sqrt A / scale r A (R + f)) = (scale r A (R + f))^2 := by
    simpa only [add_assoc] using heq
  rwa [hsum] at h

/-- Scalar data simultaneously saturate the optimized floor and every Young
bound; changing the convex weights cannot improve the first regime. -/
theorem young_family_floor_attained {r A R f : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ R + f) (e : ℝ) (he : 0 ≤ e) :
    ∃ D E F : ℝ, 0 ≤ D ∧ f ≤ E ∧
      (∀ x : ℝ, 0 < x → (r - x) * D - (A / x + R) ≤ E) ∧
      |F - E| ≤ e * (D + 1) ∧ F = f - e * (1 + (scale r A (R + f))^2) := by
  refine ⟨(scale r A (R + f))^2, f, f - e * (1 + (scale r A (R + f))^2),
    sq_nonneg _, le_rfl, ?_, ?_, rfl⟩
  · intro x hx
    have h := family_bound hr hA hq hx
    linarith only [h]
  · rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
    exact le_of_eq (by ring)

/-- Beyond the intersection regime a single Young parameter pays the entire
perturbation and gives the tail of the optimal floor. -/
lemma young_family_tail_floor {r A R M D E F e : ℝ} (he : e < r)
    (hc : ∀ x : ℝ, 0 < x → (r - x) * D - (A / x + R) * M ≤ E)
    (hp : -e * (D + M) ≤ F - E) :
    (-R - e - A / (r - e)) * M ≤ F := by
  have h := hc (r - e) (sub_pos.mpr he)
  nlinarith only [h, hp]


private lemma quadratic_family {A : ℝ} (hA : 0 ≤ A) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    -x * t^2 - A / x ≤ -2 * Real.sqrt A * t := by
  apply (mul_le_mul_iff_right₀ hx).mp
  have he : x * (-x * t^2 - A / x) = -(x * t)^2 - A := by field_simp [hx.ne']
  rw [he]
  have hsq := sq_nonneg (x * t - Real.sqrt A)
  have hu2 := Real.sq_sqrt hA
  nlinarith only [hsq, hu2]

private lemma quadratic_energy_ge_floor {r A R f t : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ R + f)
    (ht : scale r A (R + f) ≤ t) :
    f ≤ r * t^2 - 2 * Real.sqrt A * t - R := by
  obtain ⟨hs, he, hrel⟩ := scale_properties hr hA hq
  have hv := Real.sqrt_nonneg (A + r * (R + f))
  have hrt := mul_le_mul_of_nonneg_left ht hr.le
  have hsum : 0 ≤ r * (t + scale r A (R + f)) - 2 * Real.sqrt A := by
    linarith only [he, hrt, hv]
  have hp := mul_nonneg (sub_nonneg.mpr ht) hsum
  nlinarith only [hp, hrel]

/-- The tail floor is attained simultaneously against the whole Young family. -/
theorem young_family_tail_attained {r A R f e : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ R + f)
    (he : r - Real.sqrt A / scale r A (R + f) ≤ e) (her : e < r) :
    ∃ D E F : ℝ, 0 ≤ D ∧ f ≤ E ∧
      (∀ x : ℝ, 0 < x → (r - x) * D - (A / x + R) ≤ E) ∧
      |F - E| ≤ e * (D + 1) ∧ F = -R - e - A / (r - e) := by
  obtain ⟨hs, _, _⟩ := scale_properties hr hA hq
  obtain ⟨_, hxr, _⟩ := optimal_parameter_properties hr hA hq
  have he0 : 0 ≤ e := (sub_pos.mpr hxr).le.trans he
  have hx : 0 < r - e := sub_pos.mpr her
  let t := Real.sqrt A / (r - e)
  have ht : scale r A (R + f) ≤ t := by
    apply (le_div_iff₀ hx).mpr
    have he' : r - e ≤ Real.sqrt A / scale r A (R + f) := by linarith only [he]
    have h := (le_div_iff₀ hs).mp he'
    simpa only [mul_comm] using h
  let E := r * t^2 - 2 * Real.sqrt A * t - R
  refine ⟨t^2, E, E - e * (t^2 + 1), sq_nonneg _,
    quadratic_energy_ge_floor hr hA hq ht, ?_, ?_, ?_⟩
  · intro x hxp
    have h := quadratic_family hA.le t hxp
    dsimp only [E]
    linarith only [h]
  · rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (mul_nonneg he0 (by positivity))]
  · dsimp only [E, t]
    have hu2 := Real.sq_sqrt hA.le
    have hmul := congrArg (fun z : ℝ => z * (r - e)) hu2
    field_simp [hx.ne']
    nlinarith only [hmul]

/-- Once the perturbation exhausts the prime-defect reserve, the same scalar
constraints admit arbitrarily negative energies. -/
theorem young_family_unbounded_below {r A R f e : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ R + f) (he : r ≤ e) (K : ℝ) :
    ∃ D E F : ℝ, 0 ≤ D ∧ f ≤ E ∧
      (∀ x : ℝ, 0 < x → (r - x) * D - (A / x + R) ≤ E) ∧
      |F - E| ≤ e * (D + 1) ∧ F < K := by
  obtain ⟨hs, _, _⟩ := scale_properties hr hA hq
  have hu : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  let t := scale r A (R + f) + (|K + R + e| + 1) / (2 * Real.sqrt A)
  have ht : scale r A (R + f) ≤ t := le_add_of_nonneg_right (by positivity)
  have htlarge : |K + R + e| + 1 ≤ 2 * Real.sqrt A * t := by
    dsimp only [t]
    have heq : 2 * Real.sqrt A * ((|K + R + e| + 1) / (2 * Real.sqrt A)) =
        |K + R + e| + 1 := by field_simp [hu.ne']
    have hp := mul_nonneg (by positivity : 0 ≤ 2 * Real.sqrt A) hs.le
    rw [mul_add, heq]
    linarith only [hp]
  let E := r * t^2 - 2 * Real.sqrt A * t - R
  refine ⟨t^2, E, E - e * (t^2 + 1), sq_nonneg _,
    quadratic_energy_ge_floor hr hA hq ht, ?_, ?_, ?_⟩
  · intro x hxp
    have h := quadratic_family hA.le t hxp
    dsimp only [E]
    linarith only [h]
  · rw [sub_sub_cancel_left, abs_neg,
      abs_of_nonneg (mul_nonneg (hr.le.trans he) (by positivity))]
  · have hcost := mul_le_mul_of_nonneg_right he (sq_nonneg t)
    have habs := neg_abs_le (K + R + e)
    dsimp only [E]
    linarith only [hcost, htlarge, habs]


/-- A nonnegative optimized floor automatically leaves room in the reserve,
provided the mass cost is nonnegative. -/
lemma nonnegative_floor_implies_reserve {r A R f e : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ R + f) (hR : 0 ≤ R)
    (hfloor : 0 ≤ f - e * (1 + (scale r A (R + f))^2)) :
    e < r - Real.sqrt A / scale r A (R + f) := by
  obtain ⟨hx, hxr, heq⟩ := optimal_parameter_properties hr hA hq
  have ha : 0 < r - Real.sqrt A / scale r A (R + f) := sub_pos.mpr hxr
  have heq' := (div_eq_iff ha.ne').mp heq
  have hquot : 0 < A / (Real.sqrt A / scale r A (R + f)) := div_pos hA hx
  by_contra hnot
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
    (show 0 ≤ 1 + (scale r A (R + f))^2 by positivity)
  nlinarith only [hm, heq', hfloor, ha, hquot, hR]

/-- Exact positivity criterion for the full scalar bound family. This includes
all Young parameters, with no possible second positive regime. -/
theorem positive_uniform_floor_iff {r A R f e : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hq : 0 ≤ R + f) (hR : 0 ≤ R) (he : 0 ≤ e) :
    (∃ η : ℝ, 0 < η ∧ ∀ D E F : ℝ, 0 ≤ D → f ≤ E →
      (∀ x : ℝ, 0 < x → (r - x) * D - (A / x + R) ≤ E) →
      |F - E| ≤ e * (D + 1) → η ≤ F) ↔
      0 < f - e * (1 + (scale r A (R + f))^2) := by
  constructor
  · rintro ⟨η, hη, h⟩
    obtain ⟨D, E, F, hD, hf, hc, hp, hF⟩ := young_family_floor_attained hr hA hq e he
    have hb := h D E F hD hf hc hp
    rw [hF] at hb
    exact hη.trans_le hb
  · intro hpos
    refine ⟨f - e * (1 + (scale r A (R + f))^2), hpos, ?_⟩
    intro D E F _ hf hc hp
    have ha := nonnegative_floor_implies_reserve hr hA hq hR hpos.le
    have hb := floor_of_young_family (M := 1) hr hA hq he ha.le
      (by simpa only [mul_one] using hf)
      (fun x hx => by simpa only [mul_one] using hc x hx)
      (by simpa only [neg_mul] using (abs_le.mp hp).1)
    simpa only [mul_one] using hb


/-- Less reserve or larger mass costs can only increase the optimal defect
ceiling. Compare both families at the second family's minimizing parameter. -/
theorem scale_sq_mono {r₁ r₂ A₁ A₂ q₁ q₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hr : r₂ ≤ r₁) (hA : A₁ ≤ A₂) (hq : q₁ ≤ q₂) :
    (scale r₁ A₁ q₁)^2 ≤ (scale r₂ A₂ q₂)^2 := by
  obtain ⟨x, hx, hxr, heq⟩ := family_attained hr₂ hA₂ hq₂
  have hnum := (div_eq_iff (sub_pos.mpr hxr).ne').mp heq
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hxr)).mp
  calc
    (r₂ - x) * (scale r₁ A₁ q₁)^2 ≤ (r₁ - x) * (scale r₁ A₁ q₁)^2 :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hr x) (sq_nonneg _)
    _ ≤ A₁ / x + q₁ := family_bound hr₁ hA₁ hq₁ hx
    _ ≤ A₂ / x + q₂ := add_le_add (div_le_div_of_nonneg_right hA hx.le) hq
    _ = (r₂ - x) * (scale r₂ A₂ q₂)^2 := by rw [hnum, mul_comm]


open Filter Topology Set

/-- Strict relaxation of the optimized coefficient survives small errors in
reference floor, defect reserve and perturbation size. -/
lemma exists_relaxed_floor_coefficient {f B a e L : ℝ} (ha : 0 < a)
    (hL : f - e * (1 + (B + f) / a) = L) (ε : ℝ) (hε : 0 < ε) (hea : e < a) :
    ∃ τ : ℝ, 0 < τ ∧ 2 * τ < a - e ∧
      L - ε < f - τ - (e + τ) * (1 + (B + f) / (a - τ)) := by
  let g := fun τ : ℝ => f - τ - (e + τ) * (1 + (B + f) / (a - τ))
  have hg : ContinuousAt g 0 := by
    apply (continuousAt_const.sub continuousAt_id).sub
    apply (continuousAt_const.add continuousAt_id).mul
    apply continuousAt_const.add
    exact continuousAt_const.div (continuousAt_const.sub continuousAt_id)
      (by simpa only [sub_zero] using ha.ne')
  have hg0 : g 0 = L := by simpa only [g, sub_zero, add_zero] using hL
  have hlim : Tendsto g (𝓝 0) (𝓝 L) := hg0 ▸ hg.tendsto
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hlim.eventually (lt_mem_nhds (sub_lt_self L hε)))
  let τ := min (η / 2) ((a - e) / 4)
  have hτ : 0 < τ := lt_min (half_pos hη) (div_pos (sub_pos.mpr hea) (by norm_num))
  refine ⟨τ, hτ, ?_, ?_⟩
  · have h := min_le_right (η / 2) ((a - e) / 4)
    change τ ≤ (a - e) / 4 at h
    linarith only [h, hea]
  · apply hnear
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
    exact (min_le_left _ _).trans_lt (half_lt_self hη)

end GaloisForLFunctions.HTGeometry.YoungDefect


#print axioms GaloisForLFunctions.HTGeometry.YoungDefect.optimal_young_loss

#print axioms GaloisForLFunctions.HTGeometry.YoungDefect.young_family_tail_attained

#print axioms GaloisForLFunctions.HTGeometry.YoungDefect.young_family_unbounded_below

#print axioms GaloisForLFunctions.HTGeometry.YoungDefect.positive_uniform_floor_iff

#print axioms GaloisForLFunctions.HTGeometry.YoungDefect.scale_sq_mono

#print axioms GaloisForLFunctions.HTGeometry.YoungDefect.exists_relaxed_floor_coefficient
