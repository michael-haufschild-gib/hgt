import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOnPrimePairs
import GaloisForLFunctions.CountingHolography.Sections.ProperPowerContactWindows

/-!
# Removing all proper powers from the prime-pair section test

At a fixed lower degree each spline atom samples a multiplicative window
of bounded width. Chebyshev's bound on proper powers controls the contact
mass in that window. Summing over the lower degree costs only the bounded
logarithmic mass of each atom. For effective divisors the resulting bound
is quadratic in total multiplicity, uniformly in all conductor degrees.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticFunction AbsoluteGeometryOfSpecZ
open BiScaleUncertainty.ChebyshevGauge
open scoped ArithmeticFunction.vonMangoldt

private def atomWidth : ℝ := Real.exp (Real.log 3 + 5 + 4)

private def meshAtom {N : ℕ} (i : Fin N) (n j : ℕ) : ℝ :=
  cubicSpline (Real.log ((j : ℝ) / n) - (Real.log 3 + 5) - Real.log ((i : ℝ) + 1))

private theorem sample_eq_atoms {N : ℕ} (a : Fin N → ℤ) (n j : ℕ) :
    degreeSample (packet a) n j = ∑ i, (a i : ℝ) * meshAtom i n j := rfl

private theorem atomWidth_ge_one : 1 ≤ atomWidth := by
  apply Real.one_le_exp
  linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]

private theorem atom_window {N n : ℕ} (hn : 0 < n) (i : Fin N) (j : ℕ)
    (hne : meshAtom i n j ≠ 0) :
    (n : ℝ) * ((i : ℝ) + 1) ≤ j ∧ (j : ℝ) ≤ atomWidth * (n * ((i : ℝ) + 1)) := by
  let q := (i : ℝ) + 1
  let s := Real.log 3 + 5
  have hq : 1 ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) i.val]
  have hs : 4 ≤ s := by dsimp [s]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hnorm : |Real.log ((j : ℝ) / n) - s - Real.log q| ≤ 4 :=
    le_of_not_gt fun h => hne (cubicSpline_eq_zero h)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hnorm
  have hj : j ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, zero_div, Real.log_zero] at hlo
    dsimp [s] at hlo
    linarith [Real.log_nonneg hq, Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ht : 0 < (j : ℝ) / n := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)) hn'
  have hq' : 0 < q := zero_lt_one.trans_le hq
  have hl := Real.exp_le_exp.mpr (show Real.log q ≤ Real.log ((j : ℝ) / n) by linarith only [hs,hlo])
  rw [Real.exp_log hq', Real.exp_log ht] at hl
  have hu := Real.exp_le_exp.mpr
    (show Real.log ((j : ℝ) / n) ≤ (s + 4) + Real.log q by linarith only [hhi])
  rw [Real.exp_log ht, Real.exp_add, Real.exp_log hq'] at hu
  change (n : ℝ) * q ≤ j ∧ (j : ℝ) ≤ Real.exp (s+4) * (n*q)
  exact ⟨by linarith only [(le_div_iff₀ hn').mp hl],
    by linarith only [(div_le_iff₀ hn').mp hu]⟩

private def properCost : ℝ := 3 * (Real.log 4 + 4) * atomWidth

/-- All effective spline divisors obey the same quadratic bound for the
proper-power rows, including when the horizon and mesh vary independently. -/
theorem properContactMass_le {N : ℕ} (a : Fin N → ℤ) (ha : ∀ i, 0 ≤ a i)
    (L n : ℕ) (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k ∧ ¬ k.Prime) :
    ∑ k ∈ S, contactMultiplicity (packet a) L n k * Λ k ≤
      (2 * atomWidth * properCost) * (∑ i, (a i : ℝ))^2 := by
  let J := Ioc n (n+L*n)
  let f := degreeSample (packet a) n
  let c := fun i => (a i : ℝ)
  let M := ∑ i, c i
  have hc (i : Fin N) : 0 ≤ c i := by exact_mod_cast ha i
  have hM : 0 ≤ M := sum_nonneg fun i _ => hc i
  have hD := atomWidth_ge_one
  have hC : 0 ≤ properCost := by unfold properCost atomWidth; positivity
  by_cases hn : n = 0
  · subst n
    simp only [contactMultiplicity, mul_zero, add_zero, Ioc_self, sum_empty, mul_zero, zero_mul,
      sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hD)) hC) (sq_nonneg _)
  have hn' := Nat.pos_of_ne_zero hn
  have hx (i : Fin N) : 0 < (n : ℝ) * ((i : ℝ)+1) := by positivity
  have ha1 (i : Fin N) (j : ℕ) : meshAtom i n j ≤ 1 :=
    (cubicSpline_le_half _).trans (by norm_num)
  have hfr (j : ℕ) : f j = ∑ i, c i * meshAtom i n j := sample_eq_atoms a n j
  have hf0 (j : ℕ) : 0 ≤ f j := by
    rw [hfr]; exact sum_nonneg fun i _ => mul_nonneg (hc i) (cubicSpline_nonneg _)
  have hmass : ∑ j ∈ J, f j / j ≤ atomWidth*M := by
    simp_rw [hfr, sum_div, mul_div_assoc]
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro i _
    rw [← mul_sum, mul_comm atomWidth]
    exact mul_le_mul_of_nonneg_left (harmonicSample_le J (hx i) (zero_le_one.trans hD)
      (ha1 i) (atom_window hn' i)) (hc i)
  have hrow (j : ℕ) (hj : j ∈ J) : ∑ k ∈ S, (Λ k / Real.sqrt k) * f (j*k) ≤ properCost*M := by
    have hj' : 0 < j := hn'.trans (mem_Ioc.mp hj).1
    simp_rw [hfr, mul_sum]
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro i _
    calc ∑ k ∈ S, (Λ k / Real.sqrt k) * (c i * meshAtom i n (j*k))
        = c i * ∑ k ∈ S, (Λ k / Real.sqrt k) * meshAtom i n (j*k) := by
          rw [mul_sum]
          exact sum_congr rfl fun k _ => by ring
      _ ≤ c i * properCost := mul_le_mul_of_nonneg_left
          (properPowerSample_le S _ hj' hS (hx i) hD (ha1 i) (atom_window hn' i)) (hc i)
      _ = _ := mul_comm _ _
  have h := properPowerPairing_le S J f f (mul_nonneg hC hM) hf0 hrow hmass
  refine h.trans (le_of_eq ?_)
  change 2 * (atomWidth*M) * (properCost*M) = (2*atomWidth*properCost)*M^2
  ring

/-- Integral section modulus using only residue conditions at ordinary prime degrees. -/
def ordinaryPrimeModulus {N : ℕ} (a : Fin N → ℤ) : ℕ :=
  ∏ k ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime, contactBase k ^
    ⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k⌋₊

private theorem log_modulusOn (S : Finset ℕ) (e : ℕ → ℕ) :
    Real.log ((∏ k ∈ S, contactBase k ^ e k : ℕ) : ℝ) = ∑ k ∈ S, (e k : ℝ) * Λ k := by
  push_cast
  rw [Real.log_prod (fun k _ => (pow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℝ) < _) _).ne')]
  simp only [Real.log_pow, log_contactBase]

/-- Removing repeated prime powers costs at most one uniform multiple of the
square of total multiplicity, for every effective divisor. -/
theorem effective_modulus_difference_bound :
    ∃ C : ℝ, ∀ (N : ℕ) (a : Fin N → ℤ), (∀ i, 0 ≤ a i) →
      0 ≤ Real.log (contactModulus a) - Real.log (ordinaryPrimeModulus a) ∧
      Real.log (contactModulus a) - Real.log (ordinaryPrimeModulus a) ≤ C * (∑ i, (a i : ℝ))^2 := by
  refine ⟨2*atomWidth*properCost, fun N a ha => ?_⟩
  let L := 3*windowEnd N
  let n := resolution a
  let S := (Icc 2 L).filter (fun k => ¬ k.Prime)
  let x := fun k => contactMultiplicity (packet a) L n k
  have hx (k : ℕ) : 0 ≤ x k := by
    have hf (j : ℕ) : 0 ≤ degreeSample (packet a) n j := by
      rw [sample_eq_atoms]
      exact sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast ha i) (cubicSpline_nonneg _)
    unfold x contactMultiplicity
    exact mul_nonneg (by positivity) (sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (hf _) (hf _)) (Nat.cast_nonneg _))
  have he : Real.log (contactModulus a) - Real.log (ordinaryPrimeModulus a) =
      ∑ k ∈ S, (⌊x k⌋₊ : ℝ) * Λ k := by
    unfold contactModulus ordinaryPrimeModulus
    rw [log_modulusOn, log_modulusOn]
    exact sub_eq_iff_eq_add.mpr ((sum_filter_add_sum_filter_not (Icc 2 L) Nat.Prime
      (fun k => (⌊x k⌋₊ : ℝ) * Λ k)).symm.trans (add_comm _ _))
  rw [he]
  refine ⟨sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg, ?_⟩
  refine (sum_le_sum (fun k (_ : k ∈ S) =>
    mul_le_mul_of_nonneg_right (Nat.floor_le (hx k)) vonMangoldt_nonneg)).trans ?_
  apply properContactMass_le a ha L n S
  intro k hk
  obtain ⟨hkI, hkp⟩ := mem_filter.mp hk
  exact ⟨lt_of_lt_of_le (by decide : 0 < 2) (mem_Icc.mp hkI).1, hkp⟩

/-- The uniform cofinal section test on effective prime pairs needs only
ordinary prime contact rows. The constant is independent of both primes
and multiplicities. -/
theorem riemannHypothesis_iff_ordinary_prime_modulus_bound :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ p : ℕ, p.Prime →
      ∃ᶠ m : ℕ in atTop, Real.log (ordinaryPrimeModulus (m • primePair p)) ≤
        radius (m • primePair p) + B * (m : ℝ)^2 := by
  obtain ⟨C, hC⟩ := effective_modulus_difference_bound
  have hpos (p m : ℕ) (i : Fin (p+1)) : 0 ≤ (m • primePair p) i := by
    simp only [primePair, Pi.smul_apply, nsmul_eq_mul, Pi.add_apply, Pi.single_apply]
    split_ifs <;> positivity
  have hm (p m : ℕ) : (∑ i, ((m • primePair p) i : ℝ)) = 2*(m : ℝ) := by
    simp [primePair, Pi.smul_apply, Pi.single_apply, mul_add, sum_add_distrib,
      Pi.add_apply, two_mul]
  rw [riemannHypothesis_iff_prime_modulus_bound]
  constructor
  · rintro ⟨B,h⟩
    refine ⟨B, fun p hp => (h p hp).mono fun m hx => ?_⟩
    linarith only [hx, (hC _ _ (hpos p m)).1]
  · rintro ⟨B,h⟩
    refine ⟨B + 4*C, fun p hp => (h p hp).mono fun m hx => ?_⟩
    have he := (hC _ _ (hpos p m)).2
    rw [hm] at he
    linarith only [he,hx]

#print axioms effective_modulus_difference_bound
#print axioms riemannHypothesis_iff_ordinary_prime_modulus_bound

end GaloisForLFunctions.CountingHolography.Sections
