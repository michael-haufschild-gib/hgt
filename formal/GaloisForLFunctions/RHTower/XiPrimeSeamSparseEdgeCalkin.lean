import GaloisForLFunctions.RHTower.XiPrimeSeamOneEndedCollapse
import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner

/-!
# The sparse-edge Sonin Calkin chain for the canonical prime seam

The coboundary corner of an edge of the prime graph is the seam jump times the two-prime positive
Euler Gram entry.  That Gram entry has essential norm at least the product of its Euler
coefficients, so the Euler-weighted modulus of the seam jump bounds the distance of the coboundary
from every compact operator.  Compactness of one edge coboundary therefore forces the two endpoint
seam charges to agree.

Combining this with the one-ended collapse gives the sparse chain: compactness of the coboundary on
all but finitely many edges of an infinite preconnected one-ended prime graph — in particular
eventual compactness along the increasing prime ray — pins the critical line at that divisor point.
-/

namespace RHTower

noncomputable section

/-- Equation `(7)`: the canonical seam coboundary corner of an edge, a scalar multiple of the
two-scale positive Euler Gram entry. -/
def xiSeamCoboundaryCorner (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) (c : ℂ) :
    evenSubspace →L[ℂ] evenSubspace :=
  c • evenCentralPositiveEulerQuadraticCorner a p q hp hq

theorem norm_eulerCoefficientProduct (p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    ‖star (-((Real.sqrt p : ℂ)⁻¹)) * (-((Real.sqrt q : ℂ)⁻¹))‖ =
      1 / (Real.sqrt p * Real.sqrt q) := by
  have hp0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  have hq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr (zero_lt_one.trans hq)
  rw [norm_mul, norm_star, norm_neg, norm_neg, norm_inv, norm_inv,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hp0, abs_of_pos hq0]
  field_simp

/-- **Equation `(8)`.**  The Euler-weighted modulus of the seam jump is a lower bound for the
distance of the edge coboundary from every compact operator. -/
theorem norm_div_le_norm_xiSeamCoboundaryCorner_sub_compact
    {a p q : ℝ} (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (c : ℂ)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    ‖c‖ / (Real.sqrt p * Real.sqrt q) ≤ ‖xiSeamCoboundaryCorner a p q hp hq c - K‖ := by
  have hp0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  have hq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr (zero_lt_one.trans hq)
  set b : ℂ := star (-((Real.sqrt p : ℂ)⁻¹)) * (-((Real.sqrt q : ℂ)⁻¹)) with hb_def
  have hbnorm : ‖b‖ = 1 / (Real.sqrt p * Real.sqrt q) :=
    norm_eulerCoefficientProduct p q hp hq
  have hbne : b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hbnorm
    have : (0:ℝ) < 1 / (Real.sqrt p * Real.sqrt q) := by positivity
    linarith [hbnorm ▸ this]
  rcases eq_or_ne c 0 with rfl | hc
  · have hz : ‖(0 : ℂ)‖ / (Real.sqrt p * Real.sqrt q) = 0 := by simp
    rw [hz]
    exact norm_nonneg (xiSeamCoboundaryCorner a p q hp hq 0 - K)
  · have hcb : c * b ≠ 0 := mul_ne_zero hc hbne
    have hsmul : xiSeamCoboundaryCorner a p q hp hq c =
        (c * b) • evenCentralSoninQuadraticCorner a p q hp hq := by
      rw [xiSeamCoboundaryCorner, evenCentralPositiveEulerQuadraticCorner_eq_smul, smul_smul]
    have hbound := norm_smul_le_norm_smul_sub_compact_of_one_le (c * b) hcb
      (evenCentralSoninQuadraticCorner a p q hp hq) K
      (one_le_norm_evenCentralSoninQuadraticCorner_sub_compact a p q ha hp hq) hK
    rw [hsmul]
    calc ‖c‖ / (Real.sqrt p * Real.sqrt q) = ‖c * b‖ := by
          rw [norm_mul, hbnorm]; ring
      _ ≤ ‖(c * b) • evenCentralSoninQuadraticCorner a p q hp hq - K‖ := hbound

/-- A compact edge coboundary has vanishing seam jump. -/
theorem eq_zero_of_isCompactOperator_xiSeamCoboundaryCorner
    {a p q : ℝ} (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) {c : ℂ}
    (hcomp : IsCompactOperator (xiSeamCoboundaryCorner a p q hp hq c)) : c = 0 := by
  have hp0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  have hq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr (zero_lt_one.trans hq)
  have hbound := norm_div_le_norm_xiSeamCoboundaryCorner_sub_compact ha hp hq c
    (xiSeamCoboundaryCorner a p q hp hq c) hcomp
  have hb0 : ‖xiSeamCoboundaryCorner a p q hp hq c -
      xiSeamCoboundaryCorner a p q hp hq c‖ = 0 := by
    rw [sub_self]
    exact ContinuousLinearMap.opNorm_zero
  rw [hb0] at hbound
  have hcnorm : ‖c‖ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < ‖c‖ / (Real.sqrt p * Real.sqrt q) := by positivity
    linarith
  exact norm_le_zero_iff.mp hcnorm

/-! ## The prime graph -/

theorem one_lt_natPrime_cast (p : Nat.Primes) : 1 < ((p : ℕ) : ℝ) := by
  exact_mod_cast p.prop.one_lt

/-- The canonical seam coboundary of an ordered pair of primes. -/
def primeSeamCoboundary (a : ℝ) (rho : ℂ) (p q : Nat.Primes) :
    evenSubspace →L[ℂ] evenSubspace :=
  xiSeamCoboundaryCorner a ((p : ℕ) : ℝ) ((q : ℕ) : ℝ)
    (one_lt_natPrime_cast p) (one_lt_natPrime_cast q)
    (orbitwiseNatPrimeSeamCharge (p : ℕ) rho - orbitwiseNatPrimeSeamCharge (q : ℕ) rho)

/-- **Compactness forces exact endpoint coherence.** -/
theorem seamCharge_eq_of_isCompactOperator_primeSeamCoboundary
    {a : ℝ} (ha : 0 < a) {rho : ℂ} {p q : Nat.Primes}
    (hcomp : IsCompactOperator (primeSeamCoboundary a rho p q)) :
    orbitwiseNatPrimeSeamCharge (p : ℕ) rho = orbitwiseNatPrimeSeamCharge (q : ℕ) rho :=
  sub_eq_zero.mp (eq_zero_of_isCompactOperator_xiSeamCoboundaryCorner ha
    (one_lt_natPrime_cast p) (one_lt_natPrime_cast q) hcomp)

/-- **Equation `(9)`, graph form.**  On an infinite preconnected one-ended prime graph, compactness
of the seam coboundary on all but finitely many edges pins the critical line. -/
theorem re_eq_half_of_finite_noncompact_seam_edges
    {G : SimpleGraph Nat.Primes} (hconn : G.Preconnected)
    (hG : GaloisForLFunctions.HTGeometry.FiniteBoundaryOneEnded G)
    {a : ℝ} (ha : 0 < a) {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hfin : {e : Nat.Primes × Nat.Primes | G.Adj e.1 e.2 ∧
        ¬ IsCompactOperator (primeSeamCoboundary a rho e.1 e.2)}.Finite) :
    rho.re = 1 / 2 := by
  refine re_eq_half_of_finite_seam_edgeVariation hconn hG hstrip (hfin.subset ?_)
  rintro ⟨p, q⟩ ⟨hadj, hne⟩
  exact ⟨hadj, fun hcomp => hne (seamCharge_eq_of_isCompactOperator_primeSeamCoboundary ha hcomp)⟩

/-- The increasing prime enumeration as a prime-indexed family. -/
def primeRayPoint (n : ℕ) : Nat.Primes := ⟨primeRay n, primeRay_prime n⟩

@[simp] theorem primeRayPoint_coe (n : ℕ) : ((primeRayPoint n : Nat.Primes) : ℕ) = primeRay n := rfl

/-- **Equation `(9)`, ray form.**  Eventual compactness of the adjacent-prime coboundaries along
the increasing prime enumeration already pins the critical line. -/
theorem re_eq_half_of_eventually_compact_primeRay_coboundary
    {a : ℝ} (ha : 0 < a) {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hray : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsCompactOperator (primeSeamCoboundary a rho (primeRayPoint n) (primeRayPoint (n + 1)))) :
    rho.re = 1 / 2 := by
  obtain ⟨N, hN⟩ := hray
  refine re_eq_half_of_eventually_const_primeRay_seam hstrip ⟨N, fun n hn => ?_⟩
  simpa using seamCharge_eq_of_isCompactOperator_primeSeamCoboundary ha (hN n hn)

end

end RHTower
