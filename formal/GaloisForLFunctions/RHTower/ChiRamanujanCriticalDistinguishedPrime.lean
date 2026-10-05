import GaloisForLFunctions.RHTower.ChiRamanujanCriticalFiniteAtoms
/-!
# Exact distinguished-prime Fourier coefficients of the critical source

Differentiating the actual finite square-sieved source yields the distinguished
prime factor log(p)*(U_p-U_(p^2)), with delta-U_q at every other prime. This leaf
proves that factorization for every integer Fourier mode, including zero and
uncovered integers. No band limit, damping premise or cancellation bound is
assumed. Reduced rational node weights and the growing physical signed trace
remain separate obligations.
-/

noncomputable section
open Filter Set ArithmeticFunction
open scoped BigOperators Topology
namespace RHTower.BAGTrace


def ramanujanTorsionIndicator (d n : ℕ) : ℝ := if d ∣ n then 1 else 0

private lemma radical_prime_member {P : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hd : p ∣ ramanujanPrimeRadical P) : p ∈ P.filter Nat.Prime := by
  have hn : ramanujanPrimeRadical P ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q hq => (Finset.mem_filter.mp hq).2.ne_zero)
  have hf : (ramanujanPrimeRadical P).primeFactors=P.filter Nat.Prime :=
    Nat.primeFactors_prod (fun q hq => (Finset.mem_filter.mp hq).2)
  rw [← hf]
  exact (Nat.mem_primeFactors_of_ne_zero hn).mpr ⟨hp,hd⟩

theorem ramanujanSquareSieveWeight_eq_primeProduct (P : Finset ℕ) (n : ℕ) :
    ramanujanSquareSieveWeight P n =
      ∏ p ∈ P.filter Nat.Prime, (1-ramanujanTorsionIndicator (p^2) n) := by
  have he : Squarefree (ramanujanSquareSieveGcd P n) ↔
      ∀ p ∈ P.filter Nat.Prime, ¬p^2 ∣ n := by
    rw [Nat.squarefree_iff_prime_squarefree]
    constructor
    · intro h p hp hd
      have hpQ : p ∣ ramanujanPrimeRadical P := Finset.dvd_prod_of_mem _ hp
      apply h p (Finset.mem_filter.mp hp).2
      simpa only [ramanujanSquareSieveGcd,pow_two] using Nat.dvd_gcd (pow_dvd_pow_of_dvd hpQ 2) hd
    · intro h p hp hd
      have hd2 : p^2 ∣ ramanujanSquareSieveGcd P n := by simpa only [pow_two] using hd
      have hdQ : p ∣ ramanujanPrimeRadical P := hp.dvd_of_dvd_pow
        ((dvd_pow_self p (by omega : 2 ≠ 0)).trans (hd2.trans (Nat.gcd_dvd_left _ _)))
      exact h p (radical_prime_member hp hdQ) (hd2.trans (Nat.gcd_dvd_right _ _))
  rw [ramanujanSquareSieveWeight_eq_indicator]
  by_cases h : ∀ p ∈ P.filter Nat.Prime, ¬p^2 ∣ n
  · rw [if_pos (he.mpr h)]
    symm
    apply Finset.prod_eq_one
    intro p hp
    simp [ramanujanTorsionIndicator,h p hp]
  · rw [if_neg (fun hs => h (he.mp hs))]
    push Not at h
    obtain ⟨p,hp,hd⟩ := h
    symm
    exact Finset.prod_eq_zero hp (by simp [ramanujanTorsionIndicator,hd])

private lemma finiteMultiplier_product (P : Finset ℕ) (ε : ℝ) (n : ℕ) :
    ramanujanFiniteMultiplier P ε n =
      ∏ p ∈ P.filter Nat.Prime,
        (1-Real.exp (-ε*Real.log p)*ramanujanTorsionIndicator p n) := by
  have he : ramanujanFiniteIncidence P n=(P.filter Nat.Prime).filter (fun p => p ∣ n) := by
    ext p
    simp [ramanujanFiniteIncidence,and_assoc]
  rw [ramanujanFiniteMultiplier,woldSieveNormalFactor,he,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hd : p ∣ n <;> simp [ramanujanTorsionIndicator,hd]

private def sievedFactor (p n : ℕ) (ε : ℝ) : ℝ :=
  (1-ramanujanTorsionIndicator (p^2) n)*
    (1-Real.exp (-ε*Real.log p)*ramanujanTorsionIndicator p n)

private lemma sievedFactor_zero (p n : ℕ) :
    sievedFactor p n 0 = 1-ramanujanTorsionIndicator p n := by
  by_cases hd : p ∣ n
  · simp [sievedFactor,ramanujanTorsionIndicator,hd]
  · have hd2 : ¬p^2 ∣ n := fun h => hd ((dvd_pow_self p (by omega : 2 ≠ 0)).trans h)
    simp [sievedFactor,ramanujanTorsionIndicator,hd,hd2]

private lemma sievedFactor_deriv (p n : ℕ) :
    HasDerivAt (sievedFactor p n)
      (Real.log p*(ramanujanTorsionIndicator p n-ramanujanTorsionIndicator (p^2) n)) 0 := by
  change HasDerivAt (fun ε : ℝ =>
    (1-ramanujanTorsionIndicator (p^2) n)*
      (1-Real.exp (-ε*Real.log p)*ramanujanTorsionIndicator p n)) _ 0
  by_cases hd : p ∣ n
  · simpa [sievedFactor,ramanujanTorsionIndicator,hd,mul_comm] using
      (hasDerivAt_woldSievePrimeFactor p).const_mul (1-ramanujanTorsionIndicator (p^2) n)
  · have hd2 : ¬p^2 ∣ n := fun h => hd ((dvd_pow_self p (by omega : 2 ≠ 0)).trans h)
    simpa [sievedFactor,ramanujanTorsionIndicator,hd,hd2] using (hasDerivAt_const (0 : ℝ) (1 : ℝ))

/-- Each distinguished prime has the Fourier multiplier of U_p-U_(p^2). -/
def ramanujanDistinguishedPrimeMultiplier (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P.filter Nat.Prime,
    Real.log p*(ramanujanTorsionIndicator p n-ramanujanTorsionIndicator (p^2) n)*
      ∏ q ∈ (P.filter Nat.Prime).erase p, (1-ramanujanTorsionIndicator q n)

private lemma sieved_multiplier_deriv (P : Finset ℕ) (n : ℕ) :
    HasDerivAt (fun ε : ℝ => ramanujanSquareSieveWeight P n*ramanujanFiniteMultiplier P ε n)
      (ramanujanDistinguishedPrimeMultiplier P n) 0 := by
  have he (ε : ℝ) : ramanujanSquareSieveWeight P n*ramanujanFiniteMultiplier P ε n =
      ∏ p ∈ P.filter Nat.Prime, sievedFactor p n ε := by
    rw [ramanujanSquareSieveWeight_eq_primeProduct,finiteMultiplier_product,← Finset.prod_mul_distrib]
    rfl
  simp_rw [he]
  simpa only [ramanujanDistinguishedPrimeMultiplier,sievedFactor_zero,smul_eq_mul,mul_comm] using
    HasDerivAt.fun_finsetProd (u := P.filter Nat.Prime) (fun p _ => sievedFactor_deriv p n)

theorem tendsto_ramanujanPrimeOnlyMultiplier_distinguished (P : Finset ℕ) (n : ℕ) :
    Tendsto (fun ε : ℝ => ramanujanPrimeOnlyMultiplier P ε n) (𝓝[>] (0 : ℝ))
      (𝓝 (ramanujanDistinguishedPrimeMultiplier P n)) := by
  apply (sieved_multiplier_deriv P n).tendsto_slope_zero_right.congr'
  filter_upwards [] with ε
  simp only [ramanujanPrimeOnlyMultiplier,ramanujanCompensatedMultiplier,zero_add,smul_eq_mul]
  ring

/-- All integer frequencies, including zero and uncovered integers, are retained. -/
theorem sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished (P : Finset ℕ) (n : ℤ) :
    (∑ a : RamanujanPrimeOnlyAtomIndex P, (ramanujanCriticalPrimeAtomWeight P a : ℂ)*
      ramanujanFourierPhase n (ramanujanPrimeOnlyAtomNode a)) =
      (ramanujanDistinguishedPrimeMultiplier P n.natAbs : ℂ) := by
  have ha := tendsto_finsetSum Finset.univ (fun a _ =>
    (Complex.continuous_ofReal.tendsto _ |>.comp
      (tendsto_ramanujanPrimeOnlyAtomWeight_zero P a)).mul_const
        (ramanujanFourierPhase n (ramanujanPrimeOnlyAtomNode a)))
  apply tendsto_nhds_unique ha
  convert (Complex.continuous_ofReal.tendsto _ |>.comp
    (tendsto_ramanujanPrimeOnlyMultiplier_distinguished P n.natAbs)) using 1
  funext ε
  simp only [Function.comp_apply,sum_ramanujanPrimeOnlyAtomWeight_fourier]

end RHTower.BAGTrace
