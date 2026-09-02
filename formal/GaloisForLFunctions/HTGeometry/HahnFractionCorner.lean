import GaloisForLFunctions.HTGeometry.HahnFractionLeadingCoefficient

/-!
# Coordinatewise corners in Hahn fraction fields

This strengthens a single lexicographic leading term to a coordinatewise Newton corner. Corner
data is stable under field operations and coordinate differentiation. Normalizing denominator
degree exposes the exact extra derivative drop in coordinates absent from the boundary monomial.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

/-- Coordinatewise Newton-corner datum: every supported exponent is componentwise above `d`, and
the boundary coefficient at `d` is `c`. -/
def HasCornerAt {N : ℕ} (f : HahnSeries (mgDeg N) ℂ) (d : mgDeg N) (c : ℂ) : Prop :=
  (∀ k, f.coeff k ≠ 0 → ∀ j, ofLex d j ≤ ofLex k j) ∧ f.coeff d = c

theorem HasCornerAt.toHasLeadAt {N : ℕ} {f : HahnSeries (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (h : HasCornerAt f d c) : HasLeadAt f d c := by
  constructor
  · intro k hk
    by_contra hne
    have hle : d ≤ k := by
      change toLex (ofLex d) ≤ toLex (ofLex k)
      exact Pi.toLex_monotone (h.1 k hne)
    exact (not_lt_of_ge hle) hk
  · exact h.2

theorem hasCornerAt_single {N : ℕ} (d : mgDeg N) (c : ℂ) :
    HasCornerAt (HahnSeries.single d c) d c := by
  constructor
  · intro k hk j
    by_cases hkd : k = d
    · subst k
      exact le_rfl
    · rw [HahnSeries.coeff_single_of_ne hkd] at hk
      exact (hk rfl).elim
  · rw [HahnSeries.coeff_single_same]

theorem HasCornerAt.add {N : ℕ} {f g : HahnSeries (mgDeg N) ℂ}
    {d : mgDeg N} {c a : ℂ} (hf : HasCornerAt f d c) (hg : HasCornerAt g d a) :
    HasCornerAt (f + g) d (c + a) := by
  constructor
  · intro k hk j
    by_cases hfk : f.coeff k = 0
    · have hgk : g.coeff k ≠ 0 := by
        intro hg0
        apply hk
        rw [HahnSeries.coeff_add, hfk, hg0, add_zero]
      exact hg.1 k hgk j
    · exact hf.1 k hfk j
  · rw [HahnSeries.coeff_add, hf.2, hg.2]

theorem HasCornerAt.neg {N : ℕ} {f : HahnSeries (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (hf : HasCornerAt f d c) : HasCornerAt (-f) d (-c) := by
  constructor
  · intro k hk j
    apply hf.1 k _ j
    intro hf0
    apply hk
    rw [HahnSeries.coeff_neg, hf0, neg_zero]
  · rw [HahnSeries.coeff_neg, hf.2]

theorem HasCornerAt.sub {N : ℕ} {f g : HahnSeries (mgDeg N) ℂ}
    {d : mgDeg N} {c a : ℂ} (hf : HasCornerAt f d c) (hg : HasCornerAt g d a) :
    HasCornerAt (f - g) d (c - a) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem HasCornerAt.mul {N : ℕ} {f g : HahnSeries (mgDeg N) ℂ}
    {d e : mgDeg N} {c a : ℂ} (hf : HasCornerAt f d c) (hg : HasCornerAt g e a) :
    HasCornerAt (f * g) (d + e) (c * a) := by
  constructor
  · intro k hk l
    have hks : k ∈ (f * g).support := by
      simpa [HahnSeries.mem_support] using hk
    obtain ⟨i, hi, j, hj, rfl⟩ := HahnSeries.support_mul_subset hks
    exact add_le_add (hf.1 i hi l) (hg.1 j hj l)
  · exact (hf.toHasLeadAt.mul hg.toHasLeadAt).2

theorem HasCornerAt.coordinateDerivative {N : ℕ} {f : HahnSeries (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (hf : HasCornerAt f d c) (j : Fin N) :
    HasCornerAt (mgPartial N j f) (d + mgStep N j)
      (((ofLex d j : ℤ) : ℂ) * c) := by
  constructor
  · intro γ hγ l
    let k := γ - mgStep N j
    have hidx : k + mgStep N j = γ := by
      dsimp [k]
      abel
    have hcoeff := coeff_mgPartial N j f k
    rw [hidx] at hcoeff
    have hfk : f.coeff k ≠ 0 := by
      intro hk0
      apply hγ
      rw [hcoeff, hk0, mul_zero]
    have hle := hf.1 k hfk l
    rw [← hidx]
    exact add_le_add hle le_rfl
  · rw [coeff_mgPartial, hf.2]

/-- If the boundary monomial is independent of coordinate `j`, differentiation is two degrees
smaller in that coordinate: the constant exponent is killed and the first surviving integral
exponent is at least one. -/
theorem HasCornerAt.mgPartial_of_component_zero {N : ℕ}
    {f : HahnSeries (mgDeg N) ℂ} {d : mgDeg N} {c : ℂ}
    (hf : HasCornerAt f d c) (j : Fin N) (hdj : ofLex d j = 0) :
    HasCornerAt (mgPartial N j f) (d + mgStep N j + mgStep N j)
      ((mgPartial N j f).coeff (d + mgStep N j + mgStep N j)) := by
  refine ⟨?_, rfl⟩
  intro γ hγ l
  let k := γ - mgStep N j
  have hidx : k + mgStep N j = γ := by
    dsimp [k]
    abel
  have hcoeff := coeff_mgPartial N j f k
  rw [hidx] at hcoeff
  have hprod : ((ofLex k j : ℤ) : ℂ) * f.coeff k ≠ 0 := by
    rw [← hcoeff]
    exact hγ
  have hfk : f.coeff k ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hkj0 : ofLex k j ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hprod).1
  have hkjnonneg : 0 ≤ ofLex k j := by
    simpa [hdj] using hf.1 k hfk j
  have hkjpos : 0 < ofLex k j := lt_of_le_of_ne hkjnonneg (Ne.symm hkj0)
  rw [← hidx]
  by_cases hlj : l = j
  · subst l
    have hs : ofLex (mgStep N j) j = 1 := by simp [mgStep]
    change ofLex d j + ofLex (mgStep N j) j + ofLex (mgStep N j) j ≤
      ofLex k j + ofLex (mgStep N j) j
    rw [hdj, hs]
    omega
  · have hs : ofLex (mgStep N j) l = 0 := by simp [mgStep, hlj]
    change ofLex d l + ofLex (mgStep N j) l + ofLex (mgStep N j) l ≤
      ofLex k l + ofLex (mgStep N j) l
    simpa [hs] using hf.1 k hfk l

/-- Fractional coordinatewise corner datum, expressed through one numerator/denominator
presentation. -/
def FracHasCornerAt {N : ℕ} (q : HahnFraction (mgDeg N) ℂ)
    (d : mgDeg N) (c : ℂ) : Prop :=
  ∃ (f g : HahnSeries (mgDeg N) ℂ) (e : mgDeg N) (a : ℂ),
    HasCornerAt f (d + e) (c * a) ∧ HasCornerAt g e a ∧ a ≠ 0 ∧
      q = algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) f /
        algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) g

theorem FracHasCornerAt.toFracHasLeadAt {N : ℕ} {q : HahnFraction (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (h : FracHasCornerAt q d c) : FracHasLeadAt q d c := by
  obtain ⟨f, g, e, a, hf, hg, ha, hq⟩ := h
  exact ⟨f, g, e, a, hf.toHasLeadAt, hg.toHasLeadAt, ha, hq⟩

/-- Every fractional corner presentation can be normalized so that its denominator has degree
zero. -/
theorem FracHasCornerAt.normalized {N : ℕ} {q : HahnFraction (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (h : FracHasCornerAt q d c) :
    ∃ (f g : HahnSeries (mgDeg N) ℂ) (a : ℂ),
      HasCornerAt f d (c * a) ∧ HasCornerAt g 0 a ∧ a ≠ 0 ∧
        q = algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) f /
          algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) g := by
  obtain ⟨f, g, e, a, hf, hg, ha, hq⟩ := h
  let m : HahnSeries (mgDeg N) ℂ := HahnSeries.single (-e) 1
  have hm : HasCornerAt m (-e) 1 := hasCornerAt_single (-e) 1
  have hmf : HasCornerAt (m * f) d (c * a) := by
    convert hm.mul hf using 1
    · abel
    · ring
  have hmg : HasCornerAt (m * g) 0 a := by
    convert hm.mul hg using 1
    · abel
    · ring
  refine ⟨m * f, m * g, a, hmf, hmg, ha, ?_⟩
  rw [hq]
  have hm0 : algebraMap (HahnSeries (mgDeg N) ℂ)
      (HahnFraction (mgDeg N) ℂ) m ≠ 0 :=
    (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
      (HahnFraction (mgDeg N) ℂ))).mpr (hm.toHasLeadAt.ne_zero one_ne_zero)
  simp only [map_mul]
  field_simp

theorem FracHasCornerAt.of_hahn {N : ℕ} {f : HahnSeries (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (h : HasCornerAt f d c) :
    FracHasCornerAt
      (algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) f) d c := by
  refine ⟨f, 1, 0, 1, ?_, ?_, one_ne_zero, ?_⟩
  · simpa using h
  · simpa using hasCornerAt_single (N := N) 0 1
  · simp

theorem FracHasCornerAt.mul {N : ℕ} {x y : HahnFraction (mgDeg N) ℂ}
    {d e : mgDeg N} {c a : ℂ} (hx : FracHasCornerAt x d c)
    (hy : FracHasCornerAt y e a) : FracHasCornerAt (x * y) (d + e) (c * a) := by
  obtain ⟨fx, gx, dx, cx, hfx, hgx, hcx, rfl⟩ := hx
  obtain ⟨fy, gy, dy, cy, hfy, hgy, hcy, rfl⟩ := hy
  refine ⟨fx * fy, gx * gy, dx + dy, cx * cy, ?_, hgx.mul hgy,
    mul_ne_zero hcx hcy, ?_⟩
  · convert hfx.mul hfy using 1
    · abel
    · ring
  · simp only [map_mul, div_eq_mul_inv]
    ring

theorem FracHasCornerAt.add {N : ℕ} {x y : HahnFraction (mgDeg N) ℂ}
    {d : mgDeg N} {c a : ℂ} (hx : FracHasCornerAt x d c)
    (hy : FracHasCornerAt y d a) : FracHasCornerAt (x + y) d (c + a) := by
  obtain ⟨fx, gx, dx, cx, hfx, hgx, hcx, rfl⟩ := hx
  obtain ⟨fy, gy, dy, cy, hfy, hgy, hcy, rfl⟩ := hy
  refine ⟨fx * gy + fy * gx, gx * gy, dx + dy, cx * cy, ?_, hgx.mul hgy,
    mul_ne_zero hcx hcy, ?_⟩
  · have hleft : HasCornerAt (fx * gy) (d + (dx + dy)) (c * (cx * cy)) := by
      convert hfx.mul hgy using 1
      · abel
      · ring
    have hright : HasCornerAt (fy * gx) (d + (dx + dy)) (a * (cx * cy)) := by
      convert hfy.mul hgx using 1
      all_goals first | rfl | abel | ring
    convert hleft.add hright using 1
    ring
  · have hgx0 : algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ) gx ≠ 0 :=
      (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ))).mpr
          (hgx.toHasLeadAt.ne_zero hcx)
    have hgy0 : algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ) gy ≠ 0 :=
      (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ))).mpr
          (hgy.toHasLeadAt.ne_zero hcy)
    simp only [map_add, map_mul]
    field_simp

theorem FracHasCornerAt.neg {N : ℕ} {x : HahnFraction (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (hx : FracHasCornerAt x d c) :
    FracHasCornerAt (-x) d (-c) := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hx
  refine ⟨-f, g, e, a, ?_, hg, ha, ?_⟩
  · convert hf.neg using 1
    ring
  · simp only [map_neg, neg_div]

theorem FracHasCornerAt.sub {N : ℕ} {x y : HahnFraction (mgDeg N) ℂ}
    {d : mgDeg N} {c a : ℂ} (hx : FracHasCornerAt x d c)
    (hy : FracHasCornerAt y d a) : FracHasCornerAt (x - y) d (c - a) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem FracHasCornerAt.inv {N : ℕ} {x : HahnFraction (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (hx : FracHasCornerAt x d c) (hc : c ≠ 0) :
    FracHasCornerAt x⁻¹ (-d) c⁻¹ := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hx
  refine ⟨g, f, d + e, c * a, ?_, hf, mul_ne_zero hc ha, ?_⟩
  · convert hg using 1
    · abel
    · field_simp
  · rw [inv_div]

theorem FracHasCornerAt.div {N : ℕ} {x y : HahnFraction (mgDeg N) ℂ}
    {d e : mgDeg N} {c a : ℂ} (hx : FracHasCornerAt x d c)
    (hy : FracHasCornerAt y e a) (ha : a ≠ 0) :
    FracHasCornerAt (x / y) (d - e) (c / a) := by
  simpa [div_eq_mul_inv, sub_eq_add_neg] using hx.mul (hy.inv ha)

theorem FracHasCornerAt.fractionCoordinateDerivative {N : ℕ} {j : Fin N}
    {q : HahnFraction (mgDeg N) ℂ} {d : mgDeg N} {c : ℂ}
    (hq : FracHasCornerAt q d c) :
    FracHasCornerAt (hahnFractionPartial N j q) (d + mgStep N j)
      (((ofLex d j : ℤ) : ℂ) * c) := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hq
  have hdf := hf.coordinateDerivative j
  have hdg := hg.coordinateDerivative j
  have hleft : HasCornerAt (mgPartial N j f * g)
      ((d + mgStep N j) + (e + e))
      ((((ofLex (d + e) j : ℤ) : ℂ) * (c * a)) * a) := by
    convert hdf.mul hg using 1
    abel
  have hright : HasCornerAt (f * mgPartial N j g)
      ((d + mgStep N j) + (e + e))
      ((c * a) * (((ofLex e j : ℤ) : ℂ) * a)) := by
    convert hf.mul hdg using 1
    all_goals first | rfl | abel
  have hnum : HasCornerAt (mgPartial N j f * g - f * mgPartial N j g)
      ((d + mgStep N j) + (e + e))
      ((((ofLex d j : ℤ) : ℂ) * c) * (a * a)) := by
    convert hleft.sub hright using 1
    have hcomp : ((ofLex (d + e) j : ℤ) : ℂ) =
        ((ofLex d j : ℤ) : ℂ) + ((ofLex e j : ℤ) : ℂ) := by
      change (((ofLex d j + ofLex e j : ℤ) : ℂ)) = _
      push_cast
      rfl
    rw [hcomp]
    ring
  refine ⟨mgPartial N j f * g - f * mgPartial N j g, g * g,
    e + e, a * a, hnum, hg.mul hg, mul_ne_zero ha ha, ?_⟩
  have hg0 : algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) g ≠ 0 :=
    (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
      (HahnFraction (mgDeg N) ℂ))).mpr (hg.toHasLeadAt.ne_zero ha)
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul, hahnFractionPartial_algebraMap, map_sub, map_mul]
  field_simp

/-- Off an active corner coordinate, the fractional derivative has a corner two coordinate steps
lower, with an unspecified boundary coefficient. -/
theorem FracHasCornerAt.exists_hahnFractionPartial_of_component_zero {N : ℕ}
    {j : Fin N} {q : HahnFraction (mgDeg N) ℂ} {d : mgDeg N} {c : ℂ}
    (hq : FracHasCornerAt q d c) (hdj : ofLex d j = 0) :
    ∃ b : ℂ, FracHasCornerAt (hahnFractionPartial N j q)
      (d + mgStep N j + mgStep N j) b := by
  obtain ⟨f, g, a, hf, hg, ha, rfl⟩ := hq.normalized
  let df := mgPartial N j f
  let dg := mgPartial N j g
  let dn := d + mgStep N j + mgStep N j
  have hdf : HasCornerAt df dn (df.coeff dn) := by
    exact hf.mgPartial_of_component_zero j hdj
  have hdg : HasCornerAt dg (mgStep N j + mgStep N j)
      (dg.coeff (mgStep N j + mgStep N j)) := by
    have hzero : ofLex (0 : mgDeg N) j = 0 := rfl
    simpa [dg] using hg.mgPartial_of_component_zero j hzero
  have hleft : HasCornerAt (df * g) dn (df.coeff dn * a) := by
    convert hdf.mul hg using 1
    abel
  have hright : HasCornerAt (f * dg) dn
      ((c * a) * dg.coeff (mgStep N j + mgStep N j)) := by
    convert hf.mul hdg using 1
    dsimp [dn]
    abel
  let bnum := df.coeff dn * a -
    (c * a) * dg.coeff (mgStep N j + mgStep N j)
  have hnum : HasCornerAt (df * g - f * dg) dn bnum := by
    exact hleft.sub hright
  let b := bnum / (a * a)
  refine ⟨b, df * g - f * dg, g * g, 0, a * a, ?_, ?_, mul_ne_zero ha ha, ?_⟩
  · convert hnum using 1
    · simp [dn]
    · dsimp [b]
      field_simp
  · convert hg.mul hg using 1
    all_goals simp
  · have hg0 : algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ) g ≠ 0 :=
      (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ))).mpr (hg.toHasLeadAt.ne_zero ha)
    rw [Derivation.leibniz_div]
    simp only [df, dg, smul_eq_mul, hahnFractionPartial_algebraMap, map_sub, map_mul]
    field_simp

end GaloisForLFunctions.HTGeometry
