import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary
import GaloisForLFunctions.RestrictedFactorizationCalculus.AlternatingCofactorDescent

/-!
# Disjoint prime mergers on the cube-root band

For each negative cofactor use its own aperture. At quotient scale `T`
the smaller factor can range from half the cube root to the square root
of `2T`. Every pair in this band is merged, for all cofactors at once.
-/

noncomputable section

open Finset Filter RHTower
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Sixth-root coordinate for a quotient cell. Its square is the cube-root
threshold and its cube is the balanced factor scale. -/
def sixthScale (X c : ℕ) : ℝ := ((X:ℝ)/c) ^ (1/6:ℝ)

theorem sixthScale_pow (X c : ℕ) : sixthScale X c ^ 6 = (X:ℝ)/c := by
  rw [sixthScale, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

private theorem sqrt_quotient_eq (X c : ℕ) : Real.sqrt ((X:ℝ)/c) = sixthScale X c ^ 3 := by
  have h := sixthScale_pow X c
  have hz : 0 ≤ sixthScale X c := Real.rpow_nonneg (by positivity) _
  rw [← h,show sixthScale X c ^ 6 = (sixthScale X c ^ 3)^2 by ring,
    Real.sqrt_sq (by positivity)]

private theorem small_factor_upper {z : ℝ} {q r : ℕ} (hz : 0 ≤ z) (hqr : q < r)
    (hprod : (q:ℝ)*r ≤ 2*z^6) : (q:ℝ) ≤ 2*z^3 := by
  have hq : (q:ℝ)^2 ≤ 2*z^6 :=
    (show (q:ℝ)^2 ≤ (q:ℝ)*r by rw [pow_two]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqr.le) (Nat.cast_nonneg q)).trans hprod
  by_contra! h
  have hv := mul_lt_mul_of_pos_right h (show 0 < (q:ℝ)+2*z^3 by
    have h' : 0 ≤ 2*z^3 := by positivity
    linarith only [h,h'])
  nlinarith only [hq,hv,pow_nonneg hz 6]

/-- The dyadic one-to-two graph simultaneously covers every ordered pair
above half the cube root in every sufficiently large quotient cell. -/
theorem exists_cube_root_exchange :
    ∃ Z : ℝ, ∀ (X : ℕ) (A : OppositeParityMatching OrderedExchange (Ioc X (2*X))),
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)), A.sources ⊆ M.sources ∧
      ∀ c ∈ Icc 1 (2*X), μ c = -1 → Z ≤ sixthScale X c → ∀ q r : ℕ,
        q.Prime → r.Prime → q < r → (∀ d ∈ c.primeFactors, d < q) →
        c*(q*r) ∈ Ioc X (2*X) → sixthScale X c ^ 2 / 2 < q → c*(q*r) ∈ M.targets := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_cubeProducts_capacity 0)
  refine ⟨max 2 T, fun X A => ?_⟩
  let K := fun c => 2 * sixthScale X c
  obtain ⟨B,M,hA,hB,hrows,_⟩ := exists_combined_cofactor_descent X K A
  refine ⟨M,hA,fun c hc hμ hz q r hq hr hqr htop hn hqlo => ?_⟩
  let z := sixthScale X c
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hz0 : 0 < z := by linarith only [hz2]
  have hc0 : (0:ℝ)<c := by exact_mod_cast (mem_Icc.mp hc).1
  have hcn := Nat.ne_of_gt (mem_Icc.mp hc).1
  have hs := sqrt_quotient_eq X c
  have h6 := sixthScale_pow X c
  change Real.sqrt ((X:ℝ)/c) = z^3 at hs
  change z^6 = (X:ℝ)/c at h6
  have hsplit : Real.sqrt ((X:ℝ)/c) / K c = z^2/2 := by
    rw [hs]; change z^3/(2*z) = z^2/2; field_simp
  have hcell {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : c*(a*b) ∈ Ioc X (2*X)) :
      b ∈ windowPrimes ((X:ℝ)/c/a) ((2*X:ℕ)/(c:ℝ)/a) := by
    have ha0 : (0:ℝ)<a := by exact_mod_cast ha.pos
    obtain ⟨h1,h2⟩ := mem_Ioc.mp hab
    refine (mem_windowPrimes (by positivity) (by positivity)).2 ⟨hb,?_,?_⟩
    · rw [div_lt_iff₀ ha0,div_lt_iff₀ hc0]
      exact_mod_cast (by simpa only [mul_comm, mul_left_comm,mul_assoc] using h1 :
        X < b*a*c)
    · rw [le_div_iff₀ ha0,le_div_iff₀ hc0]
      exact_mod_cast (by simpa only [mul_comm, mul_left_comm,mul_assoc] using h2 :
        b*a*c ≤ 2*X)
  have hbound {a b : ℕ} (hab : c*(a*b) ∈ Ioc X (2*X)) :
      (a:ℝ)*b ≤ 2*z^6 := by
    rw [h6, ← mul_div_assoc,le_div_iff₀ hc0]
    exact_mod_cast (by simpa only [mul_comm, mul_left_comm,mul_assoc] using (mem_Ioc.mp hab).2 :
      a*b*c ≤ 2*X)
  have hqu := small_factor_upper hz0.le hqr (hbound hn)
  have hw : q*r ∈ productRow (K c) X (2*X) c := by
    apply mem_filter.mpr
    refine ⟨mem_biUnion.mpr ⟨q,?_,mem_image.mpr ⟨r,hcell hq hr hn,rfl⟩⟩,
      q,r,hq,hr,hqr,rfl,hsplit ▸ hqlo,htop⟩
    apply (mem_windowPrimes (by rw [hsplit]; positivity) (by change 0 ≤ 2*z*_; positivity)).2
    refine ⟨hq,hsplit ▸ hqlo,?_⟩
    rw [hs]
    exact hqu.trans (by
      change 2*z^3 ≤ (2*z)*z^3
      nlinarith only [mul_le_mul_of_nonneg_right hz2 (pow_nonneg hz0.le 3),pow_nonneg hz0.le 3])
  have hsub : productRow (K c) X (2*X) c ⊆ cubeProducts z ((X:ℝ)/c) ((2*X:ℕ)/(c:ℝ)) := by
    intro w h
    obtain ⟨hbal,a,b,ha,hb,hab,rfl,halo,_⟩ := mem_filter.mp h
    have hI := balancedProduct_mem_interval hcn hbal
    rw [hsplit] at halo
    refine mem_biUnion.mpr ⟨a,(mem_windowPrimes (by positivity) (by positivity)).2
      ⟨ha,halo,small_factor_upper hz0.le hab (hbound hI)⟩,mem_image.mpr ⟨b,hcell ha hb hI,rfl⟩⟩
  have hu : ((2*X:ℕ):ℝ)/c = 2*z^6 := by rw [h6]; push_cast; ring
  have hcap := hT z ((le_max_right _ _).trans hz) ((X:ℝ)/c) ((2*X:ℕ)/(c:ℝ))
    h6.le (by rw [hu,← h6]; linarith only [pow_nonneg hz0.le 6]) hu.le (by
      rw [hu,← h6,pow_zero,div_one]; linarith)
  have hprime := primeRow_eq_of_product hcn (le_refl (2*X)) hw
  exact hB (hrows c hc hμ (q*r) hw (by rw [hprime]; exact (card_le_card hsub).trans hcap))

end GaloisForLFunctions.RestrictedFactorizationCalculus
