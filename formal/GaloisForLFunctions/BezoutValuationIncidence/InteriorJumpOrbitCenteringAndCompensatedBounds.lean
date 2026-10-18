import GaloisForLFunctions.BezoutValuationIncidence.OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError
import GaloisForLFunctions.BezoutValuationIncidence.BezoutPronicInteriorSawtoothAndPredecessorPeakSplit

/-!
# Conditional centering of the two-endpoint-deleted interior sawtooth

For positive jump and interior moduli `d,e`, put `g = gcd(d,e)` and `m = e/g`.
The predecessor progression `d - 1 + d*k` traverses one residue fiber in `m`
steps. Deleting the two adjacent jump residues changes its sawtooth mean to
zero when `g = 1`, and to `(e-g)/(2*e^2)` otherwise. Thus zero conditional
mean holds exactly for coprime moduli or when the interior modulus divides
all jump locations. Every proper shared factor leaves a positive correction.

Subtracting this correction gives a zero-sum periodic sequence. Its finite
prefixes are bounded by `m`; Abel summation gives a bound `m/d` against both
harmonic weights and the compensated reciprocal weights of the interior
martingale. These estimates hold at every finite observation horizon.

The final theorem applies the bound to the existing finite-cutoff BVI
interior sum, preserving arbitrary signed coefficients and displaying all
cutoff dependence. It does not assert a bound uniform in the divisor cutoff
or a strict contraction for the horizon-free arithmetic martingale.
-/

open Finset GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- The negative centered sawtooth, with both adjacent divisibility residues deleted. -/
def interiorSawtoothAtom (e n : ℕ) : ℝ :=
  if e ∣ n ∨ e ∣ n + 1 then 0 else -centeredDiscreteSawtooth e n

private theorem interiorSawtoothAtom_mod {e : ℕ} (he : 0 < e) (n : ℕ) :
    interiorSawtoothAtom e (n % e) = interiorSawtoothAtom e n := by
  simp only [interiorSawtoothAtom, Nat.dvd_iff_mod_eq_zero,
    centeredDiscreteSawtooth_eq_mod_sub_half he, Nat.mod_mod,
    Nat.add_mod, Nat.mod_mod]

private theorem sum_coprime_orbit (f : ℕ → ℝ) {m a : ℕ}
    (hm : 0 < m) (ha : Nat.Coprime a m) (b : ℕ) :
    (∑ j ∈ range m, f ((b + a * j) % m)) = ∑ j ∈ range m, f j := by
  classical
  have hinj : Set.InjOn (fun j => (b + a * j) % m) (range m : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ h
    simp only [coe_range, Set.mem_Iio] at hj₁ hj₂
    have h1 : b + a * j₁ ≡ b + a * j₂ [MOD m] := h
    have h2 := Nat.ModEq.add_left_cancel' b h1
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rwa [Nat.gcd_comm]) h2
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] using h3
  have himg : (range m).image (fun j => (b + a * j) % m) = range m := by
    refine eq_of_subset_of_card_le (fun j hj => ?_) ?_
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hj
      exact mem_range.mpr (Nat.mod_lt _ hm)
    · rw [card_image_of_injOn hinj]
  calc
    _ = ∑ j ∈ (range m).image (fun j => (b + a * j) % m), f j :=
      (sum_image (f := f) hinj).symm
    _ = _ := by rw [himg]

private theorem sum_mod_orbit_gcd (f : ℕ → ℝ) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (c : ℕ) :
    (∑ j ∈ range (e / Nat.gcd d e), f ((c + d * j) % e)) =
      ∑ j ∈ range (e / Nat.gcd d e), f (c % Nat.gcd d e + Nat.gcd d e * j) := by
  let g := Nat.gcd d e
  let m := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  have hge : g ∣ e := Nat.gcd_dvd_right d e
  have hgd : g ∣ d := Nat.gcd_dvd_left d e
  have hem : e = g * m := (Nat.mul_div_cancel' hge).symm
  have hdn : d = g * (d / g) := (Nat.mul_div_cancel' hgd).symm
  have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd he hge) hg
  have hcop : Nat.Coprime (d / g) m := Nat.coprime_div_gcd_div_gcd hg
  have hterm (j : ℕ) :
      (c + d * j) % e = c % g + g * ((c / g + d / g * j) % m) := by
    have hx : c + d * j = c % g + g * (c / g + d / g * j) := by
      conv_lhs => rw [← Nat.mod_add_div c g, hdn]
      ring
    rw [hx, hem, Nat.mod_mul, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (Nat.mod_lt _ hg), Nat.add_mul_div_left _ _ hg,
      Nat.div_eq_of_lt (Nat.mod_lt _ hg), zero_add]
  simp_rw [hterm]
  exact sum_coprime_orbit (fun j => f (c % g + g * j)) hm hcop (c / g)

private theorem interiorSawtoothAtom_residue {e r : ℕ} (hr : r < e) :
    interiorSawtoothAtom e r =
      -(((r : ℝ) - ((e : ℝ) - 1) / 2) / e) +
      (if r = 0 then -(((e : ℝ) - 1) / (2 * e)) else 0) +
      (if r + 1 = e then ((e : ℝ) - 1) / (2 * e) else 0) := by
  have he : 0 < e := by omega
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have h0 : e ∣ r ↔ r = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hr]
  have h1 : e ∣ r + 1 ↔ r + 1 = e := by
    constructor
    · intro h
      have := Nat.le_of_dvd (by omega : 0 < r + 1) h
      omega
    · intro h; rw [h]
  simp only [interiorSawtoothAtom, h0, h1, centeredDiscreteSawtooth_eq_mod_sub_half he,
    Nat.mod_eq_of_lt hr]
  by_cases hr0 : r = 0
  · subst r
    by_cases he1 : 1 = e
    · subst e; norm_num
    · simp only [he1, true_or, ite_true, ite_false, Nat.cast_zero, add_zero]
      field_simp
      ring
  · by_cases hr1 : r + 1 = e
    · have hR : (r : ℝ) + 1 = e := by exact_mod_cast hr1
      simp only [hr0, hr1, false_or, ite_true, ite_false, add_zero]
      field_simp
      nlinarith
    · simp [hr0, hr1]

private theorem sum_interior_fiber {g m : ℕ} (hg : 0 < g) (hm : 0 < m) :
    (∑ j ∈ range m, interiorSawtoothAtom (g * m) (g - 1 + g * j)) =
      if g = 1 then 0 else ((m : ℝ) - 1) / (2 * (g * m : ℕ)) := by
  have hgm : 0 < g * m := Nat.mul_pos hg hm
  have hgmR : ((g * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hgm.ne'
  have hcast : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub hg, Nat.cast_one]
  have hterm (j : ℕ) (hj : j ∈ range m) :
      interiorSawtoothAtom (g * m) (g - 1 + g * j) =
        -(((g : ℝ) - 1 + g * j - (((g * m : ℕ) : ℝ) - 1) / 2) / (g * m : ℕ)) +
        (if g = 1 ∧ j = 0 then -((((g * m : ℕ) : ℝ) - 1) / (2 * (g * m : ℕ))) else 0) +
        (if j = m - 1 then (((g * m : ℕ) : ℝ) - 1) / (2 * (g * m : ℕ)) else 0) := by
    have hjm : j < m := mem_range.mp hj
    have hr : g - 1 + g * j < g * m := by
      have : g * (j + 1) ≤ g * m := Nat.mul_le_mul_left g hjm
      nlinarith [Nat.sub_add_cancel hg]
    have h0 : g - 1 + g * j = 0 ↔ g = 1 ∧ j = 0 := by
      constructor
      · intro h
        have hz : g * j = 0 := by omega
        have : j = 0 := (Nat.mul_eq_zero.mp hz).resolve_left hg.ne'
        omega
      · rintro ⟨rfl, rfl⟩; rfl
    have h1 : g - 1 + g * j + 1 = g * m ↔ j = m - 1 := by
      have hsub : g - 1 + 1 = g := by omega
      constructor
      · intro h
        have heq : g * (j + 1) = g * m := by nlinarith
        have := Nat.eq_of_mul_eq_mul_left hg heq
        omega
      · intro h; subst j
        have := Nat.sub_add_cancel hm
        nlinarith
    simp only [interiorSawtoothAtom_residue hr, h0, h1, Nat.cast_add,
      Nat.cast_mul, hcast]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib]
  have hsum : (∑ j ∈ range m, (j : ℝ)) = (m : ℝ) * (m - 1) / 2 := by
    have h := Finset.sum_range_id_mul_two m
    have hh : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
    have hc := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hc
    rw [hh] at hc
    linarith
  have hlast : (∑ j ∈ range m, if j = m - 1 then
      (((g * m : ℕ) : ℝ) - 1) / (2 * (g * m : ℕ)) else 0) =
      (((g * m : ℕ) : ℝ) - 1) / (2 * (g * m : ℕ)) := by
    rw [sum_eq_single (m - 1)]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact False.elim (h (mem_range.mpr (by omega)))
  rw [hlast]
  simp_rw [sum_neg_distrib, ← sum_div, sum_sub_distrib, sum_add_distrib,
    sum_const, card_range, nsmul_eq_mul, ← mul_sum, hsum]
  by_cases hg1 : g = 1
  · subst g
    simp only [true_and, ite_true]
    have hzero : (∑ j ∈ range m, if j = 0 then
        -((((1 * m : ℕ) : ℝ) - 1) / (2 * (1 * m : ℕ))) else 0) =
        -((((1 * m : ℕ) : ℝ) - 1) / (2 * (1 * m : ℕ))) := by
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exact False.elim (h (mem_range.mpr hm))
    rw [hzero]
    push_cast
    field_simp
    ring
  · simp only [hg1, false_and, ite_false, sum_const_zero]
    push_cast
    field_simp
    ring

/-- The exact mean of an interior atom on a predecessor progression of positive stride. -/
def interiorJumpOrbitMean (d e : ℕ) : ℝ :=
  if Nat.gcd d e = 1 then 0
  else ((e : ℝ) - Nat.gcd d e) / (2 * (e : ℝ) ^ 2)

private theorem pred_mod_of_dvd {g d : ℕ} (hg : 0 < g) (hd : 0 < d)
    (hgd : g ∣ d) : (d - 1) % g = g - 1 := by
  obtain ⟨q, hq⟩ := hgd
  have hq0 : 0 < q := by nlinarith
  have hh : d - 1 = g - 1 + g * (q - 1) := by
    nlinarith [Nat.sub_add_cancel hd, Nat.sub_add_cancel hg, Nat.sub_add_cancel hq0]
  rw [hh, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Exact conditional sum over the reduced orbit of length `e / gcd(d,e)`. -/
theorem interiorSawtoothAtom_jump_orbit_sum (d e : ℕ+) :
    (∑ k ∈ range ((e : ℕ) / Nat.gcd d e),
      interiorSawtoothAtom e ((d : ℕ) - 1 + d * k)) =
      (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) * interiorJumpOrbitMean d e := by
  let g := Nat.gcd (d : ℕ) (e : ℕ)
  let m := (e : ℕ) / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ d.pos
  have hge : g ∣ (e : ℕ) := Nat.gcd_dvd_right d e
  have hem : (e : ℕ) = g * m := (Nat.mul_div_cancel' hge).symm
  have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd e.pos hge) hg
  have hs := sum_mod_orbit_gcd (interiorSawtoothAtom e) d.pos e.pos ((d : ℕ) - 1)
  simp_rw [interiorSawtoothAtom_mod e.pos] at hs
  rw [pred_mod_of_dvd hg d.pos (Nat.gcd_dvd_left d e)] at hs
  change (∑ k ∈ range m, interiorSawtoothAtom e ((d : ℕ) - 1 + d * k)) =
    (m : ℝ) * interiorJumpOrbitMean d e
  rw [hs]
  have hf : (∑ k ∈ range m, interiorSawtoothAtom e (g - 1 + g * k)) =
      if g = 1 then 0 else ((m : ℝ) - 1) / (2 * (e : ℝ)) := by
    simpa only [← hem] using sum_interior_fiber hg hm
  rw [hf]
  unfold interiorJumpOrbitMean
  change (if g = 1 then 0 else ((m : ℝ) - 1) / (2 * (e : ℝ))) =
    (m : ℝ) * (if g = 1 then 0 else ((e : ℝ) - g) / (2 * (e : ℝ)^2))
  split_ifs
  · ring
  · have heR : (e : ℝ) = (g : ℝ) * m := by exact_mod_cast hem
    rw [heR]
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

/-- The correction caused by the two endpoint deletions is always nonnegative. -/
theorem interiorJumpOrbitMean_nonneg (d e : ℕ+) :
    0 ≤ interiorJumpOrbitMean d e := by
  unfold interiorJumpOrbitMean
  split_ifs
  · exact le_rfl
  · apply div_nonneg _ (by positivity)
    exact sub_nonneg.mpr (by exact_mod_cast Nat.gcd_le_right (d : ℕ) e.pos)

/-- The conditional correction gains one reciprocal power of the interior modulus. -/
theorem interiorJumpOrbitMean_le (d e : ℕ+) :
    interiorJumpOrbitMean d e ≤ 1 / (2 * (e : ℝ)) := by
  have he : (0 : ℝ) < e := by exact_mod_cast e.pos
  unfold interiorJumpOrbitMean
  split_ifs
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (e : ℝ)^2)).mpr
    have hg : (0 : ℝ) ≤ Nat.gcd (d : ℕ) e := Nat.cast_nonneg _
    field_simp
    nlinarith

/-- Complete classification of zero conditional mean: coprime moduli or a full shared modulus. -/
theorem interiorJumpOrbitMean_eq_zero_iff (d e : ℕ+) :
    interiorJumpOrbitMean d e = 0 ↔ Nat.gcd (d : ℕ) e = 1 ∨
      Nat.gcd (d : ℕ) e = e := by
  have he : (0 : ℝ) < e := by exact_mod_cast e.pos
  unfold interiorJumpOrbitMean
  by_cases hg : Nat.gcd (d : ℕ) e = 1
  · simp [hg]
  · simp only [hg, ite_false, false_or, div_eq_zero_iff,
      ne_of_gt (show (0 : ℝ) < 2 * (e : ℝ)^2 by positivity), or_false,
      sub_eq_zero, Nat.cast_inj]
    exact eq_comm

/-- An infinite family of proper-overlap corrections, with their exact positive size. -/
theorem interiorJumpOrbitMean_double (d : ℕ) :
    interiorJumpOrbitMean (d + 2) (2 * (d + 2)) =
      1 / (8 * ((d : ℝ) + 2)) := by
  have hg : Nat.gcd (d + 2) (2 * (d + 2)) = d + 2 :=
    Nat.gcd_eq_left ⟨2, by ring⟩
  have hn : d + 2 ≠ 1 := by omega
  simp only [interiorJumpOrbitMean, hg, hn, ite_false, Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat]
  have hpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  field_simp
  ring

/-- Proper overlap already prevents zero conditional mean on every doubled modulus. -/
theorem interiorJumpOrbitMean_double_pos (d : ℕ) :
    0 < interiorJumpOrbitMean (d + 2) (2 * (d + 2)) := by
  rw [interiorJumpOrbitMean_double]
  positivity

private theorem interior_atom_abs_le (e : ℕ+) (n : ℕ) :
    |interiorSawtoothAtom e n| ≤ 1 / 2 := by
  unfold interiorSawtoothAtom
  split_ifs
  · simp
  · rw [abs_neg]
    exact (abs_centeredDiscreteSawtooth_lt_half e.pos n).le

private theorem interior_orbit_periodic (d e : ℕ+) :
    Function.Periodic
      (fun k => interiorSawtoothAtom e ((d : ℕ) - 1 + d * k))
      ((e : ℕ) / Nat.gcd d e) := by
  intro k
  dsimp only
  rw [← interiorSawtoothAtom_mod e.pos, ← interiorSawtoothAtom_mod e.pos
    ((d : ℕ) - 1 + d * k)]
  congr 1
  have hdiv : (e : ℕ) ∣ (d : ℕ) * ((e : ℕ) / Nat.gcd d e) := by
    have hd := Nat.gcd_dvd_left (d : ℕ) (e : ℕ)
    have he := Nat.gcd_dvd_right (d : ℕ) (e : ℕ)
    refine ⟨(d : ℕ) / Nat.gcd d e, ?_⟩
    calc
      _ = (Nat.gcd d e * ((d : ℕ) / Nat.gcd d e)) *
          ((e : ℕ) / Nat.gcd d e) := by rw [Nat.mul_div_cancel' hd]
      _ = (Nat.gcd d e * ((e : ℕ) / Nat.gcd d e)) *
          ((d : ℕ) / Nat.gcd d e) := by ring
      _ = _ := by rw [Nat.mul_div_cancel' he]
  rw [mul_add, ← add_assoc, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv,
    add_zero, Nat.mod_mod]

private theorem sum_periodic_zero_eq_remainder (a : ℕ → ℝ) (m : ℕ)
    (hp : Function.Periodic a m) (hz : ∑ k ∈ range m, a k = 0) (L : ℕ) :
    (∑ k ∈ range L, a k) = ∑ k ∈ range (L % m), a k := by
  have hshift (q j : ℕ) : a (m * q + j) = a j := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show m * (q + 1) + j = (m * q + j) + m by ring, hp, ih]
  have hfull (q : ℕ) : (∑ k ∈ range (m * q), a k) = 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, sum_range_add, ih, zero_add]
      simpa only [hshift] using hz
  conv_lhs => rw [← Nat.mod_add_div L m, add_comm]
  rw [sum_range_add, hfull, zero_add]
  apply sum_congr rfl
  intro j _
  exact hshift _ _

/-- After exact centering, every finite progression prefix is bounded by its reduced orbit length. -/
theorem abs_interiorSawtoothAtom_centered_jump_prefix_le (d e : ℕ+) (L : ℕ) :
    |∑ k ∈ range L,
      (interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) - interiorJumpOrbitMean d e)| ≤
      (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) := by
  let m := (e : ℕ) / Nat.gcd d e
  let a := fun k => interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) -
    interiorJumpOrbitMean d e
  have hg : 0 < Nat.gcd (d : ℕ) e := Nat.gcd_pos_of_pos_left _ d.pos
  have hm : 0 < m := Nat.div_pos (Nat.gcd_le_right (d : ℕ) e.pos) hg
  have hp : Function.Periodic a m := by
    intro k
    exact congrArg (fun x => x - interiorJumpOrbitMean d e) (interior_orbit_periodic d e k)
  have hz : ∑ k ∈ range m, a k = 0 := by
    simp only [a, sum_sub_distrib, interiorSawtoothAtom_jump_orbit_sum,
      sum_const, card_range, nsmul_eq_mul, m, sub_self]
  have hmean : |interiorJumpOrbitMean d e| ≤ 1 / 2 := by
    rw [abs_of_nonneg (interiorJumpOrbitMean_nonneg d e)]
    apply (interiorJumpOrbitMean_le d e).trans
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    have : (1 : ℝ) ≤ e := by exact_mod_cast e.pos
    linarith
  have ha (k : ℕ) : |a k| ≤ 1 := by
    exact (abs_sub _ _).trans (by linarith [interior_atom_abs_le e ((d : ℕ) - 1 + d * k)])
  change |∑ k ∈ range L, a k| ≤ (m : ℝ)
  rw [sum_periodic_zero_eq_remainder a m hp hz L]
  calc
    _ ≤ ∑ k ∈ range (L % m), |a k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range (L % m), (1 : ℝ) := sum_le_sum (fun k _ => ha k)
    _ = (L % m : ℕ) := by simp
    _ ≤ (m : ℝ) := by exact_mod_cast (Nat.mod_lt L hm).le

/-- The compensated reciprocal weight, extended by zero beyond the physical horizon. -/
def interiorJumpCompensatedWeight (d : ℕ+) (T k : ℕ) : ℝ :=
  max (1 / ((d : ℝ) * ((k : ℝ) + 1)) - 1 / ((T : ℝ) + 1)) 0

/-- A horizon-independent bound for one centered interior atom against the compensated jump weight. -/
theorem abs_interiorSawtoothAtom_centered_jump_compensated_le
    (d e : ℕ+) (T L : ℕ) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
      (interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) - interiorJumpOrbitMean d e)| ≤
      (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) / (d : ℝ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  have hw : ∀ k, 0 ≤ interiorJumpCompensatedWeight d T k :=
    fun _ => le_max_right _ _
  have ha : Antitone (interiorJumpCompensatedWeight d T) := by
    intro i j hij
    apply max_le_max _ le_rfl
    apply sub_le_sub_right
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hd.le
    exact_mod_cast (Nat.add_le_add_right hij 1)
  have hw0 : interiorJumpCompensatedWeight d T 0 ≤ 1 / (d : ℝ) := by
    simp only [interiorJumpCompensatedWeight, Nat.cast_zero, zero_add, mul_one]
    exact max_le (sub_le_self _ (by positivity)) (by positivity)
  have h := abs_sum_range_mul_antitone_le
    (fun k => interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) - interiorJumpOrbitMean d e)
    (interiorJumpCompensatedWeight d T) L
    (Nat.cast_nonneg ((e : ℕ) / Nat.gcd d e)) hw ha
    (fun K _ => abs_interiorSawtoothAtom_centered_jump_prefix_le d e K)
  calc
    _ ≤ _ := h
    _ ≤ (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) * (1 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hw0 (Nat.cast_nonneg _)
    _ = _ := by ring

/-- A horizon-independent harmonic bound for one exactly centered interior atom. -/
theorem abs_interiorSawtoothAtom_centered_jump_harmonic_le (d e : ℕ+) (L : ℕ) :
    |∑ k ∈ range L,
      (interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) - interiorJumpOrbitMean d e) /
        ((d : ℝ) * ((k : ℝ) + 1))| ≤
      (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) / (d : ℝ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  have hw : ∀ k : ℕ, 0 ≤ 1 / ((d : ℝ) * ((k : ℝ) + 1)) := fun _ => by positivity
  have ha : Antitone (fun k : ℕ => 1 / ((d : ℝ) * ((k : ℝ) + 1))) := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hd.le
    exact_mod_cast (Nat.add_le_add_right hij 1)
  have h := abs_sum_range_mul_antitone_le
    (fun k => interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) - interiorJumpOrbitMean d e)
    (fun k => 1 / ((d : ℝ) * ((k : ℝ) + 1))) L
    (Nat.cast_nonneg ((e : ℕ) / Nat.gcd d e)) hw ha
    (fun K _ => abs_interiorSawtoothAtom_centered_jump_prefix_le d e K)
  simpa only [Nat.cast_zero, zero_add, mul_one, div_eq_mul_inv,
    one_mul, mul_comm] using h

/-- The existing BVI interior sum is the signed linear combination of the deleted atoms. -/
theorem bezoutInteriorSawtoothSum_eq_sum_interiorSawtoothAtom
    (N n : ℕ) (c : ℕ → ℝ) :
    bezoutInteriorSawtoothSum N c n =
      ∑ e ∈ Icc 1 N, c e * interiorSawtoothAtom e n := by
  classical
  unfold bezoutInteriorSawtoothSum
  rw [sum_filter, ← sum_neg_distrib]
  apply sum_congr rfl
  intro e _
  by_cases h : e ∣ n ∨ e ∣ n + 1
  · have hn : ¬ (¬ e ∣ n ∧ ¬ e ∣ n + 1) := by tauto
    simp only [hn, ite_false, neg_zero, interiorSawtoothAtom, h, ite_true, mul_zero]
  · have hn : ¬ e ∣ n ∧ ¬ e ∣ n + 1 := by tauto
    simp [interiorSawtoothAtom, hn.1, hn.2]

/-- Finite-cutoff conditional cancellation for arbitrary signed weights, with explicit modulus dependence. -/
theorem abs_bezoutInteriorSawtoothSum_centered_jump_compensated_le
    (N T L : ℕ) (c : ℕ → ℝ) (d : ℕ+) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
      (bezoutInteriorSawtoothSum N c ((d : ℕ) - 1 + d * k) -
        ∑ e ∈ Icc 1 N, c e * interiorJumpOrbitMean d e)| ≤
      ∑ e ∈ Icc 1 N, |c e| * (((e / Nat.gcd d e : ℕ) : ℝ) / (d : ℝ)) := by
  have heq :
      (∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
        (bezoutInteriorSawtoothSum N c ((d : ℕ) - 1 + d * k) -
          ∑ e ∈ Icc 1 N, c e * interiorJumpOrbitMean d e)) =
      ∑ e ∈ Icc 1 N, c e * ∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
        (interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) - interiorJumpOrbitMean d e) := by
    calc
      _ = ∑ k ∈ range L, ∑ e ∈ Icc 1 N, c e *
          (interiorJumpCompensatedWeight d T k *
            (interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) - interiorJumpOrbitMean d e)) := by
        apply sum_congr rfl
        intro k _
        rw [bezoutInteriorSawtoothSum_eq_sum_interiorSawtoothAtom, ← sum_sub_distrib, mul_sum]
        apply sum_congr rfl
        intro e _
        ring
      _ = _ := by rw [sum_comm]; simp only [mul_sum]
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e he
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_interiorSawtoothAtom_centered_jump_compensated_le d
      ⟨e, (mem_Icc.mp he).1⟩ T L) (abs_nonneg _)

end
end GaloisForLFunctions.BezoutValuationIncidence
