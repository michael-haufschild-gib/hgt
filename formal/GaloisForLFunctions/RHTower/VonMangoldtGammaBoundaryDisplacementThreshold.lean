import GaloisForLFunctions.RHTower.SuzukiCriticalRootedBianchiCofinalNoGo
import GaloisForLFunctions.RHTower.VonMangoldtGammaInfinitePointedWard

namespace RHTower

noncomputable section

private theorem summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_of_pos
    {x : ℝ} (hx : 0 < x) :
    Summable (fun p : Nat.Primes =>
      vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ)) := by
  have hinjective : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 2) := by
    intro p q hpq
    apply Subtype.ext
    have hp2 : 2 ≤ (p : ℕ) := p.prop.two_le
    have hq2 : 2 ≤ (q : ℕ) := q.prop.two_le
    change (p : ℕ) - 2 = (q : ℕ) - 2 at hpq
    omega
  have hraw :=
    (summable_infiniteVonMangoldtGammaRawAtom hx 0).comp_injective hinjective
  apply hraw.congr
  intro p
  have hp2 : 2 ≤ (p : ℕ) := p.prop.two_le
  have hnonneg : 0 ≤
      ArithmeticFunction.vonMangoldt p / (p : ℝ) *
        Real.exp (-x * Real.log (p : ℝ)) := by
    exact mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (Real.exp_pos _).le
  change infiniteVonMangoldtGammaRawAtom x 0 ((p : ℕ) - 2) =
    vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ)
  rw [infiniteVonMangoldtGammaRawAtom]
  simp only [pow_zero, mul_one, Nat.cast_add, Nat.cast_ofNat]
  have hnat : (p : ℕ) - 2 + 2 = (p : ℕ) := by omega
  have hcast : ((((p : ℕ) - 2 : ℕ) : ℝ) + 2) = (p : ℝ) := by
    norm_cast
  rw [hnat, hcast, vonMangoldtGammaRenormalizedBoundaryCoordinate_eq hp2,
    Real.sq_sqrt hnonneg]

private theorem log_two_mul_primeHarmonic_le_rootedBianchiPrimeMassAt_of_nonpos
    {x : ℝ} (hx : x ≤ 0) (p : Nat.Primes) :
    Real.log 2 * (1 / (p : ℝ)) ≤ suzukiRootedBianchiPrimeMassAt x p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hp : 0 < (p : ℝ) := by positivity
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hp hp2
  have hexp : 1 ≤ Real.exp (-x * Real.log (p : ℝ)) := by
    exact Real.one_le_exp
      (mul_nonneg (neg_nonneg.mpr hx) hlogp)
  rw [suzukiRootedBianchiPrimeMassAt,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  calc
    Real.log 2 * (1 / (p : ℝ)) = Real.log 2 / (p : ℝ) := by ring
    _ ≤ Real.log (p : ℝ) / (p : ℝ) :=
      div_le_div_of_nonneg_right hlog hp.le
    _ ≤ (Real.log (p : ℝ) / (p : ℝ)) *
        Real.exp (-x * Real.log (p : ℝ)) :=
      le_mul_of_one_le_right (div_nonneg hlogp hp.le) hexp

private theorem not_summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    ¬Summable (fun p : Nat.Primes =>
      vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ)) := by
  intro hsum
  have hmass : Summable (fun p : Nat.Primes =>
      suzukiRootedBianchiPrimeMassAt x p) := by
    apply hsum.congr
    intro p
    have hp2 : 2 ≤ (p : ℕ) := p.prop.two_le
    have hnonneg : 0 ≤ suzukiRootedBianchiPrimeMassAt x p := by
      rw [suzukiRootedBianchiPrimeMassAt]
      exact mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
        (Real.exp_pos _).le
    rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_eq hp2,
      Real.sq_sqrt]
    · rfl
    · simpa only [suzukiRootedBianchiPrimeMassAt] using hnonneg
  have hscaled : Summable (fun p : Nat.Primes =>
      Real.log 2 * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · exact log_two_mul_primeHarmonic_le_rootedBianchiPrimeMassAt_of_nonpos hx
    · exact hmass
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (Real.log_pos one_lt_two).ne').mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- **Sharp Gamma--Bianchi displacement threshold.** The uniquely renormalized prime boundary
coordinate is square-summable exactly at positive displacement. -/
theorem summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff
    (x : ℝ) :
    Summable (fun p : Nat.Primes =>
      vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ)) ↔ 0 < x := by
  constructor
  · intro hsum
    exact lt_of_not_ge fun hx =>
      not_summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_of_nonpos
        hx hsum
  · exact summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_of_pos

/-- A prime-independent scalar multiple has finite boundary energy exactly when the scalar
vanishes or displacement lies in the positive chamber. -/
theorem summable_const_mul_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff
    (x c : ℝ) :
    Summable (fun p : Nat.Primes =>
      (c * vonMangoldtGammaRenormalizedBoundaryCoordinate x p) ^ (2 : ℕ)) ↔
      c = 0 ∨ 0 < x := by
  constructor
  · intro hsum
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have hscaled : Summable (fun p : Nat.Primes =>
          c ^ (2 : ℕ) * vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ)) := by
        apply hsum.congr
        intro p
        ring
      have hcoordinate : Summable (fun p : Nat.Primes =>
          vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ)) :=
        (summable_mul_left_iff (pow_ne_zero 2 hc)).mp hscaled
      exact
        (summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff x).1
          hcoordinate
  · rintro (rfl | hx)
    · simp
    · have hcoordinate :=
        (summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff x).2 hx
      have hscaled := hcoordinate.mul_left (c ^ (2 : ℕ))
      apply hscaled.congr
      intro p
      ring

end

end RHTower
