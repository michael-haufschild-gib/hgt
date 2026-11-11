import GaloisForLFunctions.FamilyContinuationTheory.TheCompositeSexticSymbolsAreReciprocal
import GaloisForLFunctions.FamilyContinuationTheory.ThePoissonCoefficientSplitsOverCoprimeModuli

/-!
# The sextic Gauss sums are twisted multiplicative

For `c ∈ O = ℤ[ω]`, `c ≠ 0`, the sextic symbol `χ_c(x)` depends only on `x mod c`
(`sexticSymbol_congr`), so it defines a function on `O/(c)` (`sexticResidue`), and the sextic
Gauss sum is

`g_c(h) = Σ_{d mod c} χ_c(d) ψ_c(hd)`   (`sexticGauss`).

* `sexticGauss_mul`: for coprime `c, d`, `g_{cd}(h) = χ_c(d) χ_d(c) g_c(h) g_d(h)`;
* `sexticSymbol_mul_sexticGauss`: for `u` prime to `c`, `χ_c(u) g_c(uh) = g_c(h)`.

These are the multiplicative rules of the row Gauss sums `g_s(−m)` of the cubic-theta probe:
with sextic reciprocity the cross factor `χ_c(d) χ_d(c)` is `r(d, c) χ_d(c)²`.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### Congruence and multiplicativity of the symbols -/

theorem quadIdealSymbol_congr (I : Ideal O) {x y : O} (hxy : x - y ∈ I) :
    quadIdealSymbol I x = quadIdealSymbol I y := by
  by_cases hI : I = 0
  · simp [hI, quadIdealSymbol]
  simp only [quadIdealSymbol, if_neg hI]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun P hP => ?_)
  have hle := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  by_cases hg : P.IsMaximal ∧ (2 : O) ∉ P
  · letI := hg.1
    rw [quadPrimeValue_eq P hg.2, quadPrimeValue_eq P hg.2,
      (Ideal.Quotient.eq).mpr (hle hxy)]
  · simp only [quadPrimeValue, dif_neg hg]

theorem sexticSymbol_congr {x y c : O} (hxy : c ∣ x - y) : sexticSymbol x c = sexticSymbol y c := by
  unfold sexticSymbol quadSymbol
  rw [CubicJacobi.symbol_congr hxy,
    quadIdealSymbol_congr _ (Ideal.mem_span_singleton.mpr hxy)]

theorem sexticSymbol_mul_numerator (x y c : O) :
    sexticSymbol (x * y) c = sexticSymbol x c * sexticSymbol y c := by
  unfold sexticSymbol
  rw [CubicJacobi.symbol_mul_numerator, quadSymbol_mul_numerator, map_mul]
  ring

theorem sexticSymbol_mul_denominator (x c d : O) :
    sexticSymbol x (c * d) = sexticSymbol x c * sexticSymbol x d := by
  unfold sexticSymbol
  rw [CubicJacobi.symbol_mul_denominator, quadSymbol_mul_denominator, map_mul]
  ring

/-! ### Residue functions and Gauss sums -/

/-- The sextic symbol as a function on `O/(c)`. -/
def sexticResidue (c : O) (x : O ⧸ Ideal.span {c}) : ℂ := sexticSymbol (qrep x) c

theorem sexticResidue_mk (c x : O) : sexticResidue c (Ideal.Quotient.mk _ x) = sexticSymbol x c := by
  unfold sexticResidue
  apply sexticSymbol_congr
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep]

/-- The sextic Gauss sum `g_c(h) = Σ_{d mod c} χ_c(d) ψ_c(hd)`. -/
def sexticGauss (c : O) [NeZero c] (h : O) : ℂ :=
  ∑ d : O ⧸ Ideal.span {c}, sexticResidue c d *
    principalTraceChar c (NeZero.ne c) (Ideal.Quotient.mk _ h * d)

/-- **Gauss CRT.** For coprime `c, d`: `g_{cd}(h) = χ_c(d) χ_d(c) g_c(h) g_d(h)`. -/
theorem sexticGauss_mul (c d : O) [NeZero c] [NeZero d] (hcd : IsCoprime c d) (h : O) :
    haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
    sexticGauss (c * d) h =
      sexticSymbol d c * sexticSymbol c d * sexticGauss c h * sexticGauss d h := by
  haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
  have hsplit : ∀ m : O ⧸ Ideal.span {c * d}, sexticResidue (c * d) m =
      sexticResidue c (reduceLeft c d m) * sexticResidue d (reduceRight c d m) := by
    intro m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    simp only [reduceLeft, reduceRight, Ideal.Quotient.factor_mk, sexticResidue_mk,
      sexticSymbol_mul_denominator]
  unfold sexticGauss
  simp only [hsplit]
  rw [sum_crt_mul_traceChar c d hcd]
  have hx : ∀ x : O ⧸ Ideal.span {c},
      sexticResidue c (Ideal.Quotient.mk _ d * x) = sexticSymbol d c * sexticResidue c x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, sexticResidue_mk, sexticResidue_mk, sexticSymbol_mul_numerator]
  have hy : ∀ y : O ⧸ Ideal.span {d},
      sexticResidue d (Ideal.Quotient.mk _ c * y) = sexticSymbol c d * sexticResidue d y := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, sexticResidue_mk, sexticResidue_mk, sexticSymbol_mul_numerator]
  simp only [hx, hy, mul_assoc, ← Finset.mul_sum]
  ring

/-- An element prime to `c` is a unit modulo `c`. -/
theorem isUnit_mk_of_isCoprime {u c : O} (huc : IsCoprime u c) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) u) := by
  obtain ⟨a, b, hab⟩ := huc
  refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ a, ?_⟩
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c)
  calc Ideal.Quotient.mk (Ideal.span {c}) u * Ideal.Quotient.mk _ a =
      Ideal.Quotient.mk _ (a * u + b * c) := by
        rw [map_add, map_mul, map_mul, hc0, mul_zero, add_zero, mul_comm]
    _ = 1 := by rw [hab, map_one]

/-- **The unit twist.** For `u` prime to `c`: `χ_c(u) g_c(uh) = g_c(h)`. -/
theorem sexticSymbol_mul_sexticGauss (c : O) [NeZero c] {u : O} (huc : IsCoprime u c) (h : O) :
    sexticSymbol u c * sexticGauss c (u * h) = sexticGauss c h := by
  have hu := isUnit_mk_of_isCoprime huc
  unfold sexticGauss
  rw [Finset.mul_sum, ← Equiv.sum_comp (Units.mulLeft hu.unit) (fun d => sexticResidue c d *
    principalTraceChar c (NeZero.ne c) (Ideal.Quotient.mk _ h * d))]
  refine Finset.sum_congr rfl fun d _ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  simp only [Units.mulLeft_apply, IsUnit.unit_spec]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, sexticResidue_mk, sexticResidue_mk,
    sexticSymbol_mul_numerator, show h * (u * x) = u * h * x by ring]
  ring

end GaloisForLFunctions.FamilyContinuationTheory
