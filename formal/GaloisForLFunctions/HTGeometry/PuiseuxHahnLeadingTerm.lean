import GaloisForLFunctions.HTGeometry.NewtonEdgeNonCancellation

/-!
# Leading terms of Puiseux monomials

The Puiseux field over `ℂ` is the Hahn-series field `HahnSeries ℚ ℂ`: mathlib supplies the field
structure, the leading coefficient and the order, but nothing about how a polynomial in a Puiseux
variable behaves on a single monomial.  That is the first computation a Newton--Puiseux argument
needs — substituting a candidate leading term `c U^p` into a monomial `a Y^k` produces the monomial
`a c^k U^{kp}`, whose exponent is the Newton weight and whose coefficient is the edge-polynomial
term.

Everything here is exact algebra in the Hahn-series field; no analysis and no convergence.
-/

open HahnSeries

namespace GaloisForLFunctions.HTGeometry

/-- A power of a Puiseux monomial is the monomial with scaled exponent. -/
theorem hahn_single_pow (p : ℚ) (c : ℂ) (k : ℕ) :
    (HahnSeries.single p c) ^ k = HahnSeries.single (k • p) (c ^ k) := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single, pow_succ]
      congr 1
      · rw [succ_nsmul]

/-- **Evaluating a monomial at a Puiseux monomial.**  The exponent is the Newton weight `k p` and
the coefficient is the edge-polynomial term `a c^k`. -/
theorem eval_monomial_hahn_single (a c : ℂ) (p : ℚ) (k : ℕ) :
    (Polynomial.C (HahnSeries.single (0 : ℚ) a) * Polynomial.X ^ k).eval
        (HahnSeries.single p c)
      = HahnSeries.single (k • p) (a * c ^ k) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    hahn_single_pow, HahnSeries.single_mul_single, zero_add]

/-- The coefficient of a finite sum of Puiseux monomials picks out the matching exponents. -/
theorem coeff_sum_single {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ) (g : ι → ℂ)
    (w : ℚ) :
    (∑ i ∈ s, HahnSeries.single (f i) (g i)).coeff w
      = ∑ i ∈ s, (if f i = w then g i else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j t hjt ih =>
      rw [Finset.sum_insert hjt, Finset.sum_insert hjt, HahnSeries.coeff_add, ih]
      congr 1
      by_cases h : f j = w
      · subst h
        simp
      · simp [h, Ne.symm h]

/-- **The Newton edge governs the leading coefficient.**  Substituting `c U^p` into a polynomial and
reading off the coefficient at the Newton weight `w` gives the edge-polynomial value at `c`: the sum
of `a_i c^{k_i}` over the monomials whose weight is exactly `w`. -/
theorem coeff_eval_eq_edge {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) (k : ι → ℕ)
    (p : ℚ) (c : ℂ) (w : ℚ) :
    (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
        (HahnSeries.single p c)).coeff w
      = ∑ i ∈ s, (if (k i) • p = w then a i * c ^ (k i) else 0) := by
  have hfun : ∀ i, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
      (HahnSeries.single p c) = HahnSeries.single ((k i) • p) (a i * c ^ (k i)) :=
    fun i => eval_monomial_hahn_single (a i) c p (k i)
  rw [Finset.sum_congr rfl fun i _ => hfun i]
  exact coeff_sum_single s (fun i => (k i) • p) (fun i => a i * c ^ (k i)) w

/-- **The Newton-weight coefficient is the edge polynomial evaluated at the leading coefficient.** -/
theorem coeff_eval_eq_edge_eval {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) (k : ι → ℕ)
    (p : ℚ) (c : ℂ) (w : ℚ) :
    (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
        (HahnSeries.single p c)).coeff w
      = (∑ i ∈ s.filter (fun i => (k i) • p = w),
          Polynomial.C (a i) * Polynomial.X ^ (k i)).eval c := by
  classical
  rw [coeff_eval_eq_edge, Polynomial.eval_finsetSum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- **Vanishing at the Newton weight is exactly the edge equation.**  This is the algebraic form of
the Newton--Puiseux step: a candidate leading coefficient `c` cancels the Newton weight if and only
if it is a root of the edge polynomial. -/
theorem coeff_eval_eq_zero_iff_isRoot_edge {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℕ) (p : ℚ) (c : ℂ) (w : ℚ) :
    (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
        (HahnSeries.single p c)).coeff w = 0
      ↔ (∑ i ∈ s.filter (fun i => (k i) • p = w),
          Polynomial.C (a i) * Polynomial.X ^ (k i)).IsRoot c := by
  rw [coeff_eval_eq_edge_eval]
  exact Iff.rfl

/-- **The first Newton--Puiseux step.**  If the face at weight `w` carries at least two indices with
distinct exponents and nonzero coefficients, then some nonzero leading coefficient `c` cancels that
weight exactly. -/
theorem exists_ne_zero_coeff_eval_eq_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (k : ι → ℕ) (p w : ℚ)
    (ha : ∀ i ∈ s.filter (fun i => (k i) • p = w), a i ≠ 0)
    (hinj : Set.InjOn k (s.filter (fun i => (k i) • p = w)))
    {i₁ i₂ : ι} (h1 : i₁ ∈ s.filter (fun i => (k i) • p = w))
    (h2 : i₂ ∈ s.filter (fun i => (k i) • p = w)) (hne : i₁ ≠ i₂) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
        (HahnSeries.single p c)).coeff w = 0 := by
  classical
  obtain ⟨c, hc0, hcroot⟩ :=
    exists_ne_zero_isRoot_edge (s.filter (fun i => (k i) • p = w))
      (fun i => Polynomial.C (a i)) k
      (fun i hi => Polynomial.C_ne_zero.mpr (ha i hi)) hinj h1 h2 hne
  refine ⟨c, hc0, ?_⟩
  rw [coeff_eval_eq_zero_iff_isRoot_edge]
  simpa using hcroot

/-- **Nothing lives below the Newton weight.** -/
theorem coeff_eval_eq_zero_of_lt_weight {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℕ) (p : ℚ) (c : ℂ) (w : ℚ) (hw : ∀ i ∈ s, w ≠ (k i) • p) :
    (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
        (HahnSeries.single p c)).coeff w = 0 := by
  classical
  rw [coeff_eval_eq_edge]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact if_neg fun h => hw i hi h.symm

/-- **A unique minimiser survives.**  If exactly one index attains the weight `w`, the coefficient
there is its monomial value, nonzero whenever the coefficient and the leading term are. -/
theorem coeff_eval_ne_zero_of_unique {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℕ) (p : ℚ) {c : ℂ} (hc : c ≠ 0) (w : ℚ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (ha : a i₀ ≠ 0) (hw₀ : (k i₀) • p = w)
    (huniq : ∀ i ∈ s, i ≠ i₀ → (k i) • p ≠ w) :
    (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
        (HahnSeries.single p c)).coeff w ≠ 0 := by
  classical
  rw [coeff_eval_eq_edge]
  have hsum : (∑ i ∈ s, (if (k i) • p = w then a i * c ^ (k i) else 0))
      = a i₀ * c ^ (k i₀) := by
    refine Finset.sum_eq_single_of_mem i₀ hi₀ (fun i hi hne => if_neg (huniq i hi hne)) |>.trans ?_
    exact if_pos hw₀
  rw [hsum]
  exact mul_ne_zero ha (pow_ne_zero _ hc)

/-- **The Newton weight is the order of the substituted polynomial.**  When the minimal weight is
attained exactly once and its coefficient does not vanish, the substituted polynomial has order
precisely that weight. -/
theorem orderTop_eval_eq_of_unique_min {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℕ) (p : ℚ) {c : ℂ} (hc : c ≠ 0) (w : ℚ) {i₀ : ι} (hi₀ : i₀ ∈ s) (ha : a i₀ ≠ 0)
    (hw₀ : (k i₀) • p = w) (hmin : ∀ i ∈ s, w ≤ (k i) • p)
    (huniq : ∀ i ∈ s, i ≠ i₀ → (k i) • p ≠ w) :
    (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
        (HahnSeries.single p c)).orderTop = (w : WithTop ℚ) := by
  classical
  refine HahnSeries.orderTop_eq_of_le ?_ ?_
  · rw [HahnSeries.mem_support]
    exact coeff_eval_ne_zero_of_unique s a k p hc w hi₀ ha hw₀ huniq
  · intro γ hγ
    rcases le_or_gt w γ with h | h
    · exact h
    · exfalso
      rw [HahnSeries.mem_support] at hγ
      refine hγ (coeff_eval_eq_zero_of_lt_weight s a k p c γ fun i hi heq => ?_)
      have hle := hmin i hi
      rw [← heq] at hle
      exact absurd hle (not_le.mpr h)

/-- A vanishing coefficient at a weight already known to be below the order pushes the order past
it. -/
private theorem lt_orderTop_of_coeff_eq_zero (x : HahnSeries ℚ ℂ) (w : ℚ)
    (hle : (w : WithTop ℚ) ≤ x.orderTop) (hcoeff : x.coeff w = 0) :
    (w : WithTop ℚ) < x.orderTop := by
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd hcoeff (HahnSeries.coeff_orderTop_ne h.symm)

/-- **Choosing an edge root strictly raises the order.**  This is the progress step of the
Newton--Puiseux iteration: with the minimal weight `w` and a leading coefficient `c` on the edge, the
substituted polynomial has order strictly greater than `w`. -/
theorem lt_orderTop_eval_of_isRoot_edge {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℕ) (p : ℚ) (c : ℂ) (w : ℚ) (hmin : ∀ i ∈ s, w ≤ (k i) • p)
    (hroot : (∑ i ∈ s.filter (fun i => (k i) • p = w),
        Polynomial.C (a i) * Polynomial.X ^ (k i)).IsRoot c) :
    (w : WithTop ℚ)
      < (∑ i ∈ s, (Polynomial.C (HahnSeries.single (0 : ℚ) (a i)) * Polynomial.X ^ (k i)).eval
          (HahnSeries.single p c)).orderTop := by
  classical
  refine lt_orderTop_of_coeff_eq_zero _ w ?_ ?_
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro γ hγ
    have hγw : γ < w := by exact_mod_cast hγ
    refine coeff_eval_eq_zero_of_lt_weight s a k p c γ fun i hi heq => ?_
    have hle := hmin i hi
    rw [← heq] at hle
    exact absurd hle (not_le.mpr hγw)
  · rw [coeff_eval_eq_zero_iff_isRoot_edge]
    exact hroot

/-! ## Coefficients with their own orders

The Newton polygon of a genuine algebraic equation has coefficients that are themselves Puiseux
series, contributing their own orders `d i` to the weight `d i + k i p`. -/

/-- **Evaluating a monomial with a graded coefficient.** -/
theorem eval_graded_monomial_hahn_single (a c : ℂ) (d p : ℚ) (k : ℕ) :
    (Polynomial.C (HahnSeries.single d a) * Polynomial.X ^ k).eval (HahnSeries.single p c)
      = HahnSeries.single (d + k • p) (a * c ^ k) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    hahn_single_pow, HahnSeries.single_mul_single]

/-- **Two vertices determine the slope.**  If two monomials with different exponents lie on the same
Newton face, the slope is their difference quotient — in particular it is rational with denominator
dividing the gap between the exponents. -/
theorem slope_eq_of_two_on_face {ι : Type*} (d : ι → ℚ) (k : ι → ℕ) (p : ℚ) {i₁ i₂ : ι}
    (hk : k i₁ ≠ k i₂) (h : d i₁ + (k i₁) • p = d i₂ + (k i₂) • p) :
    p = (d i₁ - d i₂) / ((k i₂ : ℚ) - (k i₁ : ℚ)) := by
  have hkne : ((k i₂ : ℚ) - (k i₁ : ℚ)) ≠ 0 := by
    intro hzero
    apply hk
    have : (k i₁ : ℚ) = (k i₂ : ℚ) := by linarith
    exact_mod_cast this
  have hsm : ∀ n : ℕ, (n • p) = (n : ℚ) * p := fun n => nsmul_eq_mul n p
  rw [hsm, hsm] at h
  field_simp
  linarith

/-! ## Bounded ramification

Newton--Puiseux iterates by substituting `single p c` and re-expanding.  For the iteration to stay
inside a *fixed* Puiseux field one must know that the exponents produced never leave a lattice
`(1/N)Z` of rationals with bounded denominator.  The slope of a Newton face is a difference quotient
of two coefficient orders divided by a gap between two exponents, so it lies in the lattice refined
by that gap — and a bounded gap gives a bounded refinement. -/

/-- The additive lattice of rationals whose denominator divides `N`. -/
noncomputable def denomLattice (N : ℕ) : AddSubgroup ℚ := AddSubgroup.zmultiples ((N : ℚ)⁻¹)

theorem mem_denomLattice_iff {N : ℕ} {q : ℚ} :
    q ∈ denomLattice N ↔ ∃ m : ℤ, q = (m : ℚ) / (N : ℚ) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hm' : (m : ℤ) • ((N : ℚ)⁻¹) = q := hm
    rw [← hm', zsmul_eq_mul, div_eq_mul_inv]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    show (m : ℤ) • ((N : ℚ)⁻¹) = q
    rw [zsmul_eq_mul, ← div_eq_mul_inv, ← hm]

theorem zero_mem_denomLattice (N : ℕ) : (0 : ℚ) ∈ denomLattice N :=
  (denomLattice N).zero_mem

/-- **The lattice refines along divisibility.**  If `N` divides `M` then every rational with
denominator dividing `N` also has denominator dividing `M`. -/
theorem denomLattice_mono {N M : ℕ} (hM : M ≠ 0) (h : N ∣ M) :
    denomLattice N ≤ denomLattice M := by
  obtain ⟨c, rfl⟩ := h
  have hN : (N : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rintro rfl
    exact hM (by simp)
  have hc : (c : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rintro rfl
    exact hM (by simp)
  intro q hq
  rw [mem_denomLattice_iff] at hq ⊢
  obtain ⟨m, hm⟩ := hq
  refine ⟨m * c, ?_⟩
  rw [hm]
  push_cast
  field_simp

/-- **The weights stay in the lattice.**  If the coefficient orders and the substituted exponent lie
in a lattice, so does every Newton weight `d + k p`. -/
theorem weight_mem_denomLattice {N : ℕ} {d p : ℚ} (k : ℕ) (hd : d ∈ denomLattice N)
    (hp : p ∈ denomLattice N) : d + k • p ∈ denomLattice N :=
  (denomLattice N).add_mem hd ((denomLattice N).nsmul_mem hp k)

/-- **The slope of a face lies in a boundedly refined lattice.**  If two monomials with exponents
`k₁ < k₂` lie on the same Newton face and their coefficient orders have denominator dividing `M`,
then the slope has denominator dividing `M (k₂ - k₁)` — in particular the refinement is controlled
by the degree of the equation. -/
theorem slope_mem_denomLattice {M : ℕ} {d₁ d₂ p : ℚ} {k₁ k₂ : ℕ}
    (hd₁ : d₁ ∈ denomLattice M) (hd₂ : d₂ ∈ denomLattice M) (hk : k₁ < k₂)
    (h : d₁ + k₁ • p = d₂ + k₂ • p) :
    p ∈ denomLattice (M * (k₂ - k₁)) := by
  obtain ⟨m₁, hm₁⟩ := mem_denomLattice_iff.mp hd₁
  obtain ⟨m₂, hm₂⟩ := mem_denomLattice_iff.mp hd₂
  have hkne : k₁ ≠ k₂ := Nat.ne_of_lt hk
  have hslope : p = (d₁ - d₂) / ((k₂ : ℚ) - (k₁ : ℚ)) :=
    slope_eq_of_two_on_face (fun b : Bool => if b then d₁ else d₂)
      (fun b : Bool => if b then k₁ else k₂) p (i₁ := true) (i₂ := false)
      (by simpa using hkne) (by simpa using h)
  have hgap : ((k₂ - k₁ : ℕ) : ℚ) = (k₂ : ℚ) - (k₁ : ℚ) := by
    have := Nat.cast_sub (le_of_lt hk) (R := ℚ)
    simpa using this
  have hdiff : d₁ - d₂ = ((m₁ - m₂ : ℤ) : ℚ) / (M : ℚ) := by
    rw [hm₁, hm₂]
    push_cast
    ring
  refine mem_denomLattice_iff.mpr ⟨m₁ - m₂, ?_⟩
  have hcast : ((M * (k₂ - k₁) : ℕ) : ℚ) = (M : ℚ) * ((k₂ : ℚ) - (k₁ : ℚ)) := by
    rw [Nat.cast_mul, hgap]
  rw [hslope, hdiff, hcast, div_div]

/-- **A uniform bound on the ramification.**  If the exponent gaps that can occur are bounded — for
instance by the degree of the equation, so that every gap divides `D` — then every face slope lies
in the single lattice `(1/(M D))Z`, independent of which face is chosen. -/
theorem slope_mem_denomLattice_of_dvd {M D : ℕ} {d₁ d₂ p : ℚ} {k₁ k₂ : ℕ} (hM : M ≠ 0) (hD : D ≠ 0)
    (hd₁ : d₁ ∈ denomLattice M) (hd₂ : d₂ ∈ denomLattice M) (hk : k₁ < k₂)
    (hdvd : (k₂ - k₁) ∣ D) (h : d₁ + k₁ • p = d₂ + k₂ • p) :
    p ∈ denomLattice (M * D) :=
  denomLattice_mono (Nat.mul_ne_zero hM hD) (mul_dvd_mul_left M hdvd)
    (slope_mem_denomLattice hd₁ hd₂ hk h)

/-- **The iteration invariant.**  Coefficient orders in `(1/M)Z` and a substituted exponent in the
refined lattice `(1/(M D))Z` produce Newton weights in that same refined lattice: one refinement
absorbs the whole iteration, so the Puiseux exponents never leave a fixed lattice. -/
theorem weight_mem_denomLattice_of_orders {M D : ℕ} (hM : M ≠ 0) (hD : D ≠ 0) {d p : ℚ} (k : ℕ)
    (hd : d ∈ denomLattice M) (hp : p ∈ denomLattice (M * D)) :
    d + k • p ∈ denomLattice (M * D) :=
  weight_mem_denomLattice k
    (denomLattice_mono (Nat.mul_ne_zero hM hD) ⟨D, rfl⟩ hd) hp

end GaloisForLFunctions.HTGeometry
