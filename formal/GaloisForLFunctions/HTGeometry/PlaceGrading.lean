import GaloisForLFunctions.HTGeometry.PlaceDerivationValuationDrop

/-!
# Degree bookkeeping at a place

The peel's degree bookkeeping on the coordinate field uses `TopDegLE m γ f`: the order of `f` at
infinity in the coordinate `m` is at least `−γ`.  At a place of an algebraic extension the same
bookkeeping is the adic valuation, with values in `ℤᵐ⁰` so that ramified places carry fractional
degrees of the base coordinate.  `PlaceDegLE v γ f` says the valuation of `f` at `v` is at most
`γ`, and `PlaceFree v f` says `f` is a unit at the place.  The lemmas are the closure properties
the border-shape induction consumes: sums, products, inverses of units, and — through the cleared
derivation of `PlaceDerivationValuationDrop` — differentiation, which costs at most the order of
the clearing element plus one.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- The valuation of `f` at the place is at most `γ`. -/
def PlaceDegLE (γ : ℤᵐ⁰) (f : K) : Prop := v.valuation K f ≤ γ

/-- `f` is a unit at the place. -/
def PlaceFree (f : K) : Prop := v.valuation K f = 1

theorem placeDegLE_zero (γ : ℤᵐ⁰) : PlaceDegLE v γ (0 : K) := by
  rw [PlaceDegLE, Valuation.map_zero]
  exact zero_le

theorem placeDegLE_one : PlaceDegLE v 1 (1 : K) := by
  rw [PlaceDegLE, Valuation.map_one]

theorem PlaceFree.placeDegLE {f : K} (h : PlaceFree v f) : PlaceDegLE v 1 f :=
  le_of_eq h

theorem PlaceDegLE.mono {γ γ' : ℤᵐ⁰} (h : γ ≤ γ') {f : K} (hf : PlaceDegLE v γ f) :
    PlaceDegLE v γ' f :=
  le_trans hf h

theorem PlaceDegLE.add {γ : ℤᵐ⁰} {f g : K} (hf : PlaceDegLE v γ f) (hg : PlaceDegLE v γ g) :
    PlaceDegLE v γ (f + g) :=
  le_trans (Valuation.map_add _ _ _) (max_le hf hg)

theorem PlaceDegLE.sub {γ : ℤᵐ⁰} {f g : K} (hf : PlaceDegLE v γ f) (hg : PlaceDegLE v γ g) :
    PlaceDegLE v γ (f - g) :=
  le_trans (Valuation.map_sub _ _ _) (max_le hf hg)

theorem PlaceDegLE.neg {γ : ℤᵐ⁰} {f : K} (hf : PlaceDegLE v γ f) : PlaceDegLE v γ (-f) := by
  rw [PlaceDegLE, Valuation.map_neg]
  exact hf

theorem PlaceDegLE.mul {γ δ : ℤᵐ⁰} {f g : K} (hf : PlaceDegLE v γ f) (hg : PlaceDegLE v δ g) :
    PlaceDegLE v (γ * δ) (f * g) := by
  rw [PlaceDegLE, Valuation.map_mul]
  exact mul_le_mul' hf hg

theorem PlaceDegLE.pow {γ : ℤᵐ⁰} {f : K} (hf : PlaceDegLE v γ f) (k : ℕ) :
    PlaceDegLE v (γ ^ k) (f ^ k) := by
  rw [PlaceDegLE, Valuation.map_pow]
  exact pow_le_pow_left' hf k

theorem PlaceFree.mul {f g : K} (hf : PlaceFree v f) (hg : PlaceFree v g) :
    PlaceFree v (f * g) := by
  rw [PlaceFree, Valuation.map_mul, hf, hg, one_mul]

theorem PlaceFree.inv {f : K} (hf : PlaceFree v f) : PlaceFree v f⁻¹ := by
  rw [PlaceFree, Valuation.map_inv, hf, inv_one]

theorem PlaceFree.ne_zero {f : K} (hf : PlaceFree v f) : f ≠ 0 := by
  intro h0
  rw [PlaceFree, h0, Valuation.map_zero] at hf
  exact zero_ne_one hf

/-- Dividing by a unit of the place does not move the degree. -/
theorem PlaceDegLE.div_placeFree {γ : ℤᵐ⁰} {f g : K} (hf : PlaceDegLE v γ f)
    (hg : PlaceFree v g) : PlaceDegLE v γ (f / g) := by
  rw [PlaceDegLE, Valuation.map_div, hg, div_one]
  exact hf

/-- **Differentiation costs at most `e` degrees at the place.**  This is the cleared-derivation
drop of `PlaceDerivationValuationDrop`, in the grading vocabulary. -/
theorem PlaceDegLE.fun_deriv {D : K → K}
    (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = x * D y + y * D x) {c : R}
    (hclear : ∀ x : R, v.valuation K (algebraMap R K c * D (algebraMap R K x)) ≤ 1)
    {e : ℕ} (hce : c ∉ v.asIdeal ^ e)
    {γ : ℤᵐ⁰} {f : K} (hf : PlaceDegLE v γ f) :
    PlaceDegLE v (γ * exp (e : ℤ)) (D f) := by
  refine le_trans (valuation_fun_le_of_not_mem_pow v hadd hmul hclear hce f) ?_
  exact mul_le_mul' hf le_rfl

/-- The exact-valuation form: a sum of a term of exact valuation `γ` and a term of strictly
smaller valuation has exact valuation `γ`.  This is what keeps a border shape's leading term
visible through the peel. -/
theorem valuation_add_of_lt {γ : ℤᵐ⁰} {f g : K} (hf : v.valuation K f = γ)
    (hg : v.valuation K g < γ) : v.valuation K (f + g) = γ := by
  rw [← hf] at hg ⊢
  exact Valuation.map_add_eq_of_lt_left _ hg

end GaloisForLFunctions.HTGeometry
