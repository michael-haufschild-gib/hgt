/-
# The shadow radical is the exact denominator of a rational logarithmic derivative

For a nonzero `h ∈ K(t)` written in lowest terms as `num/denom`, the polynomials `a` for which
`a · h′/h` is again a polynomial are exactly the multiples of `radical (denom · num)`, the
squarefree polynomial whose roots are the distinct finite zeros and poles of `h`.

Cross-multiplying `a · h′ = b · h` turns the statement into the polynomial divisibility
`denom · num ∣ a · wronskian denom num`, which
`GaloisForLFunctions.RadicalDeriv.radical_dvd_of_dvd_mul_wronskian` and
`GaloisForLFunctions.RadicalDeriv.dvd_radical_mul_wronskian` settle in both directions.

This is the exact-leading-coefficient half of the exponential--rational shadow bidegree law.
-/
import GaloisForLFunctions.HTGeometry.RadicalDerivativeDivisibility
import GaloisForLFunctions.HTGeometry.RationalExponentialShadow

noncomputable section

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain

namespace GaloisForLFunctions.RationalShadow

open GaloisForLFunctions.RadicalDeriv GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The squarefree polynomial carrying the finite zeros and poles of a rational function. -/
def shadowRadical (h : RatFunc K) : K[X] := radical (h.denom * h.num)

omit [CharZero K] [DecidableEq K] in
theorem algebraMap_denom_ne_zero (h : RatFunc K) :
    algebraMap K[X] (RatFunc K) h.denom ≠ 0 := by
  intro hzero
  exact RatFunc.denom_ne_zero h
    (IsFractionRing.injective K[X] (RatFunc K) (by simpa using hzero))

omit [CharZero K] [DecidableEq K] in
/-- **Cross-multiplied form of `a·h′ = b·h`.** -/
theorem cross_iff (h : RatFunc K) (a b : K[X]) :
    algebraMap K[X] (RatFunc K) a * ratFuncCoordinateDerivation K h
        = algebraMap K[X] (RatFunc K) b * h
      ↔ a * wronskian h.denom h.num = b * (h.denom * h.num) := by
  have hD : algebraMap K[X] (RatFunc K) h.denom ≠ 0 := algebraMap_denom_ne_zero h
  have hinj : Function.Injective (algebraMap K[X] (RatFunc K)) :=
    IsFractionRing.injective K[X] (RatFunc K)
  constructor
  · intro hab
    rw [ratFuncCoordinateDerivation_apply] at hab
    conv_rhs at hab => rw [← RatFunc.num_div_denom h]
    refine hinj ?_
    rw [wronskian]
    simp only [map_mul, map_sub]
    field_simp at hab
    linear_combination hab
  · intro hpoly
    have key : algebraMap K[X] (RatFunc K) (a * wronskian h.denom h.num)
        = algebraMap K[X] (RatFunc K) (b * (h.denom * h.num)) := by rw [hpoly]
    rw [wronskian] at key
    simp only [map_mul, map_sub] at key
    rw [ratFuncCoordinateDerivation_apply]
    conv_rhs => rw [← RatFunc.num_div_denom h]
    field_simp
    linear_combination key

/-- **Item 3, minimality.**  Any polynomial pair realising the logarithmic derivative of `h` has
its leading term divisible by the shadow radical. -/
theorem shadowRadical_dvd {h : RatFunc K} (hh : h ≠ 0) {a b : K[X]} (ha : a ≠ 0)
    (hab : algebraMap K[X] (RatFunc K) a * ratFuncCoordinateDerivation K h
        = algebraMap K[X] (RatFunc K) b * h) :
    shadowRadical h ∣ a := by
  refine radical_dvd_of_dvd_mul_wronskian (RatFunc.denom_ne_zero h) (RatFunc.num_ne_zero hh) ha
    (RatFunc.isCoprime_num_denom h).symm ⟨b, ?_⟩
  rw [(cross_iff h a b).mp hab]
  ring

omit [CharZero K] in
/-- **Item 3, attainment.**  The shadow radical itself realises the logarithmic derivative. -/
theorem exists_cross_shadowRadical (h : RatFunc K) :
    ∃ b : K[X], algebraMap K[X] (RatFunc K) (shadowRadical h)
        * ratFuncCoordinateDerivation K h = algebraMap K[X] (RatFunc K) b * h := by
  obtain ⟨b, hb⟩ :=
    dvd_radical_mul_wronskian (k := K) (RatFunc.isCoprime_num_denom h).symm
  refine ⟨b, (cross_iff h _ b).mpr ?_⟩
  rw [shadowRadical, hb]
  ring

/-- **Item 3, exact minimal degree.** -/
theorem natDegree_shadowRadical_le {h : RatFunc K} (hh : h ≠ 0) {a b : K[X]} (ha : a ≠ 0)
    (hab : algebraMap K[X] (RatFunc K) a * ratFuncCoordinateDerivation K h
        = algebraMap K[X] (RatFunc K) b * h) :
    (shadowRadical h).natDegree ≤ a.natDegree :=
  Polynomial.natDegree_le_of_dvd (shadowRadical_dvd hh ha hab) ha

end GaloisForLFunctions.RationalShadow

namespace GaloisForLFunctions.RationalShadow

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k]

theorem natDegree_radical_eq_card_roots {p : k[X]} (hp : p ≠ 0) :
    (radical p).natDegree = p.roots.toFinset.card := by
  classical
  have hr0 : radical p ≠ 0 := radical_ne_zero
  have hsep : (radical p).Separable :=
    (PerfectField.separable_iff_squarefree).mpr squarefree_radical
  have hnodup : (radical p).roots.Nodup := Polynomial.nodup_roots hsep
  have hsplits : (radical p).Splits := IsAlgClosed.splits _
  have h1 : (radical p).natDegree = Multiset.card (radical p).roots :=
    (Polynomial.splits_iff_card_roots.mp hsplits).symm
  have h2 : (radical p).roots.toFinset = p.roots.toFinset := by
    ext x
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots hr0, Polynomial.mem_roots hp,
      ← Polynomial.dvd_iff_isRoot]
    exact dvd_radical_iff_of_irreducible (Polynomial.irreducible_X_sub_C x) hp
  rw [h1, ← Multiset.toFinset_card_of_nodup hnodup, h2]


omit [CharZero k] [IsAlgClosed k] in
/-- The finite zeros and poles of a rational function. -/
theorem roots_toFinset_denom_mul_num {h : RatFunc k} (hh : h ≠ 0) :
    (h.denom * h.num).roots.toFinset = h.denom.roots.toFinset ∪ h.num.roots.toFinset := by
  classical
  rw [Polynomial.roots_mul (mul_ne_zero (RatFunc.denom_ne_zero h) (RatFunc.num_ne_zero hh)),
    Multiset.toFinset_add]

/-- **The exact minimal leading degree is the number of distinct finite zeros and poles.** -/
theorem natDegree_shadowRadical_eq_card_roots {h : RatFunc k} (hh : h ≠ 0) :
    (shadowRadical h).natDegree
      = (h.denom.roots.toFinset ∪ h.num.roots.toFinset).card := by
  rw [shadowRadical,
    natDegree_radical_eq_card_roots (mul_ne_zero (RatFunc.denom_ne_zero h)
      (RatFunc.num_ne_zero hh)),
    roots_toFinset_denom_mul_num hh]


end GaloisForLFunctions.RationalShadow
