import GaloisForLFunctions.HTGeometry.HahnFractionValuation
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# Leading coefficients in a Hahn fraction field

`FracHasLeadAt` gives presentation-independent leading data for fractions of Hahn series. Its
calculus covers field operations and the extended coordinate derivations, hence logarithmic
derivatives. The final nested-Puiseux staircase turns terminal-output and successive suffix-product
leading terms into algebraic independence over `ℂ`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field R]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem HasLeadAt.ne_zero {f : HahnSeries Γ R} {d : Γ} {c : R}
    (h : HasLeadAt f d c) (hc : c ≠ 0) : f ≠ 0 := by
  intro hf
  have := h.2
  rw [hf] at this
  exact hc this.symm

omit [IsOrderedAddMonoid Γ] in
theorem hasLeadAt_one : HasLeadAt (1 : HahnSeries Γ R) 0 1 := by
  constructor
  · intro k hk
    rw [HahnSeries.coeff_one, if_neg (ne_of_lt hk)]
  · rw [HahnSeries.coeff_one, if_pos rfl]

/-- A fraction has degree `d` and boundary coefficient `c` when it has a numerator/denominator
presentation whose degrees and coefficients differ by exactly `(d,c)`. Coefficient zero records a
lower bound, as for `HasLeadAt`. -/
def FracHasLeadAt (q : HahnFraction Γ R) (d : Γ) (c : R) : Prop :=
  ∃ (f g : HahnSeries Γ R) (e : Γ) (a : R),
    HasLeadAt f (d + e) (c * a) ∧ HasLeadAt g e a ∧ a ≠ 0 ∧
      q = algebraMap (HahnSeries Γ R) (HahnFraction Γ R) f /
        algebraMap (HahnSeries Γ R) (HahnFraction Γ R) g

theorem FracHasLeadAt.ne_zero {q : HahnFraction Γ R} {d : Γ} {c : R}
    (h : FracHasLeadAt q d c) (hc : c ≠ 0) : q ≠ 0 := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := h
  exact div_ne_zero
    ((map_ne_zero (algebraMap (HahnSeries Γ R) (HahnFraction Γ R))).mpr
      (hf.ne_zero (mul_ne_zero hc ha)))
    ((map_ne_zero (algebraMap (HahnSeries Γ R) (HahnFraction Γ R))).mpr
      (hg.ne_zero ha))

theorem FracHasLeadAt.of_hahn {f : HahnSeries Γ R} {d : Γ} {c : R}
    (h : HasLeadAt f d c) :
    FracHasLeadAt (algebraMap (HahnSeries Γ R) (HahnFraction Γ R) f) d c := by
  refine ⟨f, 1, 0, 1, ?_, hasLeadAt_one, one_ne_zero, ?_⟩
  · simpa using h
  · simp

theorem FracHasLeadAt.mul {x y : HahnFraction Γ R} {d e : Γ} {c a : R}
    (hx : FracHasLeadAt x d c) (hy : FracHasLeadAt y e a) :
    FracHasLeadAt (x * y) (d + e) (c * a) := by
  obtain ⟨fx, gx, dx, cx, hfx, hgx, hcx, rfl⟩ := hx
  obtain ⟨fy, gy, dy, cy, hfy, hgy, hcy, rfl⟩ := hy
  refine ⟨fx * fy, gx * gy, dx + dy, cx * cy, ?_, ?_, mul_ne_zero hcx hcy, ?_⟩
  · convert hfx.mul hfy using 1
    · abel
    · ring
  · exact hgx.mul hgy
  · simp only [map_mul, div_eq_mul_inv]
    ring

theorem FracHasLeadAt.add {x y : HahnFraction Γ R} {d : Γ} {c a : R}
    (hx : FracHasLeadAt x d c) (hy : FracHasLeadAt y d a) :
    FracHasLeadAt (x + y) d (c + a) := by
  obtain ⟨fx, gx, dx, cx, hfx, hgx, hcx, rfl⟩ := hx
  obtain ⟨fy, gy, dy, cy, hfy, hgy, hcy, rfl⟩ := hy
  refine ⟨fx * gy + fy * gx, gx * gy, dx + dy, cx * cy, ?_, ?_,
    mul_ne_zero hcx hcy, ?_⟩
  · have hleft : HasLeadAt (fx * gy) (d + (dx + dy)) (c * (cx * cy)) := by
      convert hfx.mul hgy using 1
      · abel
      · ring
    have hright : HasLeadAt (fy * gx) (d + (dx + dy)) (a * (cx * cy)) := by
      convert hfy.mul hgx using 1
      · abel
      · ring
    convert hleft.add hright using 1
    ring
  · exact hgx.mul hgy
  · have hgx0 : algebraMap (HahnSeries Γ R) (HahnFraction Γ R) gx ≠ 0 :=
      (map_ne_zero (algebraMap (HahnSeries Γ R) (HahnFraction Γ R))).mpr
        (hgx.ne_zero hcx)
    have hgy0 : algebraMap (HahnSeries Γ R) (HahnFraction Γ R) gy ≠ 0 :=
      (map_ne_zero (algebraMap (HahnSeries Γ R) (HahnFraction Γ R))).mpr
        (hgy.ne_zero hcy)
    simp only [map_add, map_mul]
    field_simp

theorem FracHasLeadAt.neg {x : HahnFraction Γ R} {d : Γ} {c : R}
    (hx : FracHasLeadAt x d c) : FracHasLeadAt (-x) d (-c) := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hx
  refine ⟨-f, g, e, a, ?_, hg, ha, ?_⟩
  · convert hf.neg using 1
    ring
  · simp only [map_neg, neg_div]

theorem FracHasLeadAt.sub {x y : HahnFraction Γ R} {d : Γ} {c a : R}
    (hx : FracHasLeadAt x d c) (hy : FracHasLeadAt y d a) :
    FracHasLeadAt (x - y) d (c - a) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem FracHasLeadAt.inv {x : HahnFraction Γ R} {d : Γ} {c : R}
    (hx : FracHasLeadAt x d c) (hc : c ≠ 0) :
    FracHasLeadAt x⁻¹ (-d) c⁻¹ := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hx
  refine ⟨g, f, d + e, c * a, ?_, hf, mul_ne_zero hc ha, ?_⟩
  · convert hg using 1
    · abel
    · field_simp
  · rw [inv_div]

theorem FracHasLeadAt.div {x y : HahnFraction Γ R} {d e : Γ} {c a : R}
    (hx : FracHasLeadAt x d c) (hy : FracHasLeadAt y e a) (ha : a ≠ 0) :
    FracHasLeadAt (x / y) (d - e) (c / a) := by
  simpa [div_eq_mul_inv, sub_eq_add_neg] using hx.mul (hy.inv ha)

/-- A coefficient derivation preserves Hahn degree and differentiates its boundary coefficient. -/
theorem HasLeadAt.hahnCoefficientDerivation
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) {f : HahnSeries Δ K} {d : Δ} {c : K}
    (hf : HasLeadAt f d c) :
    HasLeadAt (hahnCoefficientDerivation D f) d (D c) := by
  constructor
  · intro k hk
    rw [coeff_hahnCoefficientDerivation, hf.1 k hk, map_zero]
  · rw [coeff_hahnCoefficientDerivation, hf.2]

/-- The fraction-field coefficient derivation preserves degree and differentiates its boundary
coefficient. -/
theorem FracHasLeadAt.hahnFractionCoefficientDerivation
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) {q : HahnFraction Δ K} {d : Δ} {c : K}
    (hq : FracHasLeadAt q d c) :
    FracHasLeadAt (hahnFractionCoefficientDerivation D q) d (D c) := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hq
  have hdf := hf.hahnCoefficientDerivation D
  have hdg := hg.hahnCoefficientDerivation D
  have hleft : HasLeadAt (hahnCoefficientDerivation D f * g)
      (d + (e + e)) (D (c * a) * a) := by
    convert hdf.mul hg using 1
    abel
  have hright : HasLeadAt (f * hahnCoefficientDerivation D g)
      (d + (e + e)) ((c * a) * D a) := by
    convert hf.mul hdg using 1
    abel
  have hnum : HasLeadAt
      (hahnCoefficientDerivation D f * g - f * hahnCoefficientDerivation D g)
      (d + (e + e)) (D c * (a * a)) := by
    convert hleft.sub hright using 1
    rw [D.leibniz]
    simp only [smul_eq_mul]
    ring
  refine ⟨hahnCoefficientDerivation D f * g - f * hahnCoefficientDerivation D g,
    g * g, e + e, a * a, hnum, hg.mul hg, mul_ne_zero ha ha, ?_⟩
  have hg0 : algebraMap (HahnSeries Δ K) (HahnFraction Δ K) g ≠ 0 :=
    (map_ne_zero (algebraMap (HahnSeries Δ K) (HahnFraction Δ K))).mpr
      (hg.ne_zero ha)
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul, hahnFractionCoefficientDerivation_algebraMap, map_sub, map_mul]
  field_simp

/-- Boundary action of a coefficient-generic multigraded coordinate derivative. -/
theorem hasLeadAt_mgPartialBase {K : Type*} [Field K] [CharZero K]
    {N : ℕ} {j : Fin N} {f : HahnSeries (mgDeg N) K} {d : mgDeg N} {c : K}
    (h : HasLeadAt f d c) :
    HasLeadAt (mgPartialBase K N j f) (d + mgStep N j)
      (((ofLex d j : ℤ) : K) * c) := by
  constructor
  · intro k hk
    have hd : mgPartialBase K N j f =
        mgShiftBase K N j * hahnGrade (mgCompBase K N j) f := by
      show ((mgShiftBase K N j) • hahnDerivationBase (mgCompBase K N j)) f = _
      simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [hd, mgShiftBase, HahnSeries.coeff_single_mul, coeff_hahnGrade]
    have hlt : k - mgStep N j < d := by
      have hstep : k - mgStep N j + mgStep N j = k := by abel
      refine lt_of_add_lt_add_right (a := mgStep N j) ?_
      rw [hstep]
      exact hk
    rw [h.1 _ hlt]
    ring
  · rw [coeff_mgPartialBase, h.2]

/-- Fraction-field boundary action of a coefficient-generic coordinate derivative. -/
theorem FracHasLeadAt.hahnFractionPartialBase {K : Type*} [Field K] [CharZero K]
    {N : ℕ} {j : Fin N} {q : HahnFraction (mgDeg N) K}
    {d : mgDeg N} {c : K} (hq : FracHasLeadAt q d c) :
    FracHasLeadAt (hahnFractionPartialBase K N j q) (d + mgStep N j)
      (((ofLex d j : ℤ) : K) * c) := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hq
  have hdf := hasLeadAt_mgPartialBase (j := j) hf
  have hdg := hasLeadAt_mgPartialBase (j := j) hg
  have hleft : HasLeadAt (mgPartialBase K N j f * g)
      ((d + mgStep N j) + (e + e))
      ((((ofLex (d + e) j : ℤ) : K) * (c * a)) * a) := by
    convert hdf.mul hg using 1
    abel
  have hright : HasLeadAt (f * mgPartialBase K N j g)
      ((d + mgStep N j) + (e + e))
      ((c * a) * (((ofLex e j : ℤ) : K) * a)) := by
    convert hf.mul hdg using 1
    all_goals first | rfl | abel
  have hnum : HasLeadAt (mgPartialBase K N j f * g - f * mgPartialBase K N j g)
      ((d + mgStep N j) + (e + e))
      ((((ofLex d j : ℤ) : K) * c) * (a * a)) := by
    convert hleft.sub hright using 1
    have hcomp : ((ofLex (d + e) j : ℤ) : K) =
        ((ofLex d j : ℤ) : K) + ((ofLex e j : ℤ) : K) := by
      change (((ofLex d j + ofLex e j : ℤ) : K)) = _
      push_cast
      rfl
    rw [hcomp]
    ring
  refine ⟨mgPartialBase K N j f * g - f * mgPartialBase K N j g, g * g,
    e + e, a * a, hnum, hg.mul hg, mul_ne_zero ha ha, ?_⟩
  have hg0 : algebraMap (HahnSeries (mgDeg N) K) (HahnFraction (mgDeg N) K) g ≠ 0 :=
    (map_ne_zero (algebraMap (HahnSeries (mgDeg N) K)
      (HahnFraction (mgDeg N) K))).mpr (hg.ne_zero ha)
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul, hahnFractionPartialBase_algebraMap, map_sub, map_mul]
  field_simp

theorem FracHasLeadAt.hahnFractionPartial {N : ℕ} {j : Fin N}
    {q : HahnFraction (mgDeg N) ℂ} {d : mgDeg N} {c : ℂ}
    (hq : FracHasLeadAt q d c) :
    FracHasLeadAt (hahnFractionPartial N j q) (d + mgStep N j)
      (((ofLex d j : ℤ) : ℂ) * c) := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hq
  have hdf := hasLeadAt_mgPartial (j := j) hf
  have hdg := hasLeadAt_mgPartial (j := j) hg
  have hleft : HasLeadAt (mgPartial N j f * g)
      ((d + mgStep N j) + (e + e))
      ((((ofLex (d + e) j : ℤ) : ℂ) * (c * a)) * a) := by
    convert hdf.mul hg using 1
    abel
  have hright : HasLeadAt (f * mgPartial N j g)
      ((d + mgStep N j) + (e + e))
      ((c * a) * (((ofLex e j : ℤ) : ℂ) * a)) := by
    convert hf.mul hdg using 1
    all_goals first | rfl | abel
  have hnum : HasLeadAt (mgPartial N j f * g - f * mgPartial N j g)
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
      (HahnFraction (mgDeg N) ℂ))).mpr (hg.ne_zero ha)
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul, hahnFractionPartial_algebraMap, map_sub, map_mul]
  field_simp

theorem FracHasLeadAt.zero (d : Γ) : FracHasLeadAt (0 : HahnFraction Γ R) d 0 := by
  simpa using FracHasLeadAt.of_hahn (hasLeadAt_zero (R := R) d)

theorem FracHasLeadAt.one : FracHasLeadAt (1 : HahnFraction Γ R) 0 1 := by
  simpa using FracHasLeadAt.of_hahn (hasLeadAt_one (Γ := Γ) (R := R))

theorem FracHasLeadAt.prod {ι : Type*} [DecidableEq ι]
    (f : ι → HahnFraction Γ R) (d : ι → Γ) (c : ι → R) :
    ∀ s : Finset ι, (∀ i ∈ s, FracHasLeadAt (f i) (d i) (c i)) →
      FracHasLeadAt (∏ i ∈ s, f i) (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _
      simpa using (FracHasLeadAt.one (Γ := Γ) (R := R))
  | @insert a s ha ih =>
      intro hall
      have hfa := hall a (Finset.mem_insert_self a s)
      have hrest := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
      simpa [Finset.prod_insert ha, Finset.sum_insert ha] using hfa.mul hrest

theorem FracHasLeadAt.sum {ι : Type*} [DecidableEq ι]
    (f : ι → HahnFraction Γ R) (d : Γ) (c : ι → R) :
    ∀ s : Finset ι, (∀ i ∈ s, FracHasLeadAt (f i) d (c i)) →
      FracHasLeadAt (∑ i ∈ s, f i) d (∑ i ∈ s, c i) := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _
      simpa using (FracHasLeadAt.zero (R := R) d)
  | @insert a s ha ih =>
      intro hall
      have hfa := hall a (Finset.mem_insert_self a s)
      have hrest := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using hfa.add hrest

theorem FracHasLeadAt.unitsSMul (ε : ℤˣ) {x : HahnFraction Γ R} {d : Γ} {c : R}
    (hx : FracHasLeadAt x d c) : FracHasLeadAt (ε • x) d (ε • c) := by
  rcases Int.units_eq_one_or ε with hε | hε
  · subst ε
    simpa using hx
  · subst ε
    simpa using hx.neg

/-- Boundary leading datum of a determinant over the Hahn fraction field. -/
theorem fracHasLeadAt_det {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (HahnFraction Γ R)) (a b : Fin n → Γ)
    (L : Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, FracHasLeadAt (M i j) (a i + b j) (L i j)) :
    FracHasLeadAt M.det ((∑ i, a i) + ∑ j, b j) L.det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  refine FracHasLeadAt.sum _ ((∑ i, a i) + ∑ j, b j) _ Finset.univ ?_
  intro σ _
  have hp := FracHasLeadAt.prod (fun i => M (σ i) i)
    (fun i => a (σ i) + b i) (fun i => L (σ i) i) Finset.univ
    (fun i _ => hM (σ i) i)
  have hsum : (∑ i, (a (σ i) + b i)) = (∑ i, a i) + ∑ j, b j := by
    rw [Finset.sum_add_distrib]
    congr 1
    exact Fintype.sum_equiv σ _ _ fun i => rfl
  have hp' : FracHasLeadAt (∏ i, M (σ i) i)
      ((∑ i, a i) + ∑ j, b j) (∏ i, L (σ i) i) := by
    simpa only [hsum] using hp
  exact hp'.unitsSMul (Equiv.Perm.sign σ)

/-- A nonsingular matrix of fractional boundary coefficients certifies a nonzero determinant. -/
theorem fracDet_ne_zero_of_hasLeadAt {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (HahnFraction Γ R)) (a b : Fin n → Γ)
    (L : Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, FracHasLeadAt (M i j) (a i + b j) (L i j))
    (hL : L.det ≠ 0) : M.det ≠ 0 :=
  (fracHasLeadAt_det M a b L hM).ne_zero hL

/-! ## Nested-Puiseux cascade gradient -/

/-- Product degree of coordinates from `k` through the last coordinate. Coordinate zero is the
outermost (terminal-state) Puiseux scale. -/
def mgSuffixDegree (N k : ℕ) : mgDeg N :=
  toLex fun j => if k ≤ (j : ℕ) then (-1 : ℤ) else 0

@[simp] theorem ofLex_mgSuffixDegree (N k : ℕ) (j : Fin N) :
    ofLex (mgSuffixDegree N k) j = if k ≤ (j : ℕ) then (-1 : ℤ) else 0 := rfl

/-- Nested-Puiseux degrees of terminal output followed by its logarithmic-state chain. -/
def mgNestedCascadeObservableDegree (n : ℕ) (i : Fin (n + 1)) : mgDeg (n + 1) :=
  if i = 0 then mgUnit (n + 1) 0 else mgSuffixDegree (n + 1) (i : ℕ)

/-- Coefficient matrix of the nested-Puiseux cascade gradient. -/
def hahnFractionNestedCascadeLeadMatrix {n : ℕ} (c : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if i = 0 then (if j = 0 then -c i else 0)
    else if (i : ℕ) ≤ (j : ℕ) then -c i else 0

theorem hahnFractionNestedCascadeLeadMatrix_upper {n : ℕ}
    (c : Fin (n + 1) → ℂ) (i j : Fin (n + 1)) (hji : j < i) :
    hahnFractionNestedCascadeLeadMatrix c i j = 0 := by
  by_cases hi : i = 0
  · subst i
    exact (Fin.not_lt_zero j hji).elim
  · rw [hahnFractionNestedCascadeLeadMatrix, if_neg hi, if_neg]
    omega

theorem hahnFractionNestedCascadeLeadMatrix_diag {n : ℕ}
    (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    hahnFractionNestedCascadeLeadMatrix c i i = -c i := by
  by_cases hi : i = 0
  · subst i
    simp [hahnFractionNestedCascadeLeadMatrix]
  · rw [hahnFractionNestedCascadeLeadMatrix, if_neg hi, if_pos le_rfl]

theorem hahnFractionNestedCascadeLeadMatrix_det_ne_zero {n : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0) :
    (hahnFractionNestedCascadeLeadMatrix c).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular
    (hahnFractionNestedCascadeLeadMatrix_upper c)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    rw [hahnFractionNestedCascadeLeadMatrix_diag]
    exact neg_ne_zero.mpr (hc i)

/-- Coordinate-gradient matrix in the Hahn fraction field. -/
def hahnFractionGradientMatrix {N : ℕ}
    (f : Fin N → HahnFraction (mgDeg N) ℂ) :
    Matrix (Fin N) (Fin N) (HahnFraction (mgDeg N) ℂ) :=
  fun i j => hahnFractionPartial N j (f i)

theorem hahnFractionGradientMatrix_det_ne_zero_of_nestedCascade_leads {n : ℕ}
    (f : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hf : ∀ i, FracHasLeadAt (f i) (mgNestedCascadeObservableDegree n i) (c i)) :
    (hahnFractionGradientMatrix f).det ≠ 0 := by
  refine fracDet_ne_zero_of_hasLeadAt (hahnFractionGradientMatrix f)
    (mgNestedCascadeObservableDegree n) (fun j => mgStep (n + 1) j)
    (hahnFractionNestedCascadeLeadMatrix c) ?_
    (hahnFractionNestedCascadeLeadMatrix_det_ne_zero c hc)
  intro i j
  have h := (hf i).hahnFractionPartial (j := j)
  by_cases hi : i = 0
  · subst i
    rw [mgNestedCascadeObservableDegree, if_pos rfl] at h
    rw [mgNestedCascadeObservableDegree, if_pos rfl]
    by_cases hj : j = 0
    · subst j
      simpa [hahnFractionGradientMatrix, hahnFractionNestedCascadeLeadMatrix, mgUnit] using h
    · simpa [hahnFractionGradientMatrix, hahnFractionNestedCascadeLeadMatrix, mgUnit, hj] using h
  · rw [mgNestedCascadeObservableDegree, if_neg hi, ofLex_mgSuffixDegree] at h
    rw [mgNestedCascadeObservableDegree, if_neg hi]
    by_cases hj : (i : ℕ) ≤ (j : ℕ)
    · simpa [hahnFractionGradientMatrix, hahnFractionNestedCascadeLeadMatrix, hi, hj] using h
    · simpa [hahnFractionGradientMatrix, hahnFractionNestedCascadeLeadMatrix, hi, hj] using h

theorem algebraicIndependent_of_hahnFractionGradientMatrix_det_ne_zero {N : ℕ}
    (f : Fin N → HahnFraction (mgDeg N) ℂ)
    (hdet : (hahnFractionGradientMatrix f).det ≠ 0) :
    AlgebraicIndependent ℂ f := by
  let M : Matrix (Fin N) (Fin N) (HahnFraction (mgDeg N) ℂ) :=
    Matrix.transpose (hahnFractionGradientMatrix f)
  have hM : M.det ≠ 0 := by
    simpa [M, Matrix.det_transpose] using hdet
  refine algebraicIndependent_of_domain_jacobian f
    (fun i => hahnFractionPartial N i) ?_ ?_ ?_ M hM ?_
  · intro i a b
    exact map_add (hahnFractionPartial N i) a b
  · intro i a b
    simpa only [smul_eq_mul, add_comm, mul_comm] using
      (hahnFractionPartial N i).leibniz a b
  · intro i c
    exact (hahnFractionPartial N i).map_algebraMap c
  · intro i j
    rfl

/-- **Nested-Puiseux cascade observability in a differential field.** Terminal-output leading data
and the successive suffix-product leads of the logarithmic states force algebraic independence. -/
theorem algebraicIndependent_hahnFractionNestedCascade_of_leads {n : ℕ}
    (f : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hf : ∀ i, FracHasLeadAt (f i) (mgNestedCascadeObservableDegree n i) (c i)) :
    AlgebraicIndependent ℂ f :=
  algebraicIndependent_of_hahnFractionGradientMatrix_det_ne_zero f
    (hahnFractionGradientMatrix_det_ne_zero_of_nestedCascade_leads f c hc hf)

end GaloisForLFunctions.HTGeometry
