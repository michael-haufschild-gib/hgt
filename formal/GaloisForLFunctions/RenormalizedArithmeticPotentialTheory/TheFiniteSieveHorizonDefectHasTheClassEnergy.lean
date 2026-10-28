import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasTheTowerFinitePart

/-!
# The actual finite-sieve horizon defect has the class energy

The affine class-mass law converts the tensor polar counterterm into the
logarithmically matched ordinary norm. The resulting limit is the negative
quadratic form of `diag(log d) + gamma_Q I - P_Q` in the original class coordinates.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticIntersectionTheory ArithmeticEffectivityTheory ArithmeticElectrostatics

/-- The exact ordinary norm of a density-normalized finite class profile. -/
theorem sum_normalizedSieveProfile_sq {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d)
    (b : ι → ℝ) (M : ℕ) :
    (∑ n ∈ Icc 1 M, normalizedSieveProfile Q d b n ^ 2) =
      ∑ i, b i ^ 2 * (sieveClassMass Q (d i) M / sieveClassDensity Q (d i)) := by
  let x := normalizedSieveProfile Q d b
  let c : ι → ℝ := fun i => b i / Real.sqrt (sieveClassDensity Q (d i))
  have hnorm : (∑ n ∈ Icc 1 M, x n ^ 2) =
      ∑ i, c i * sieveClassPolar Q (d i) M x := by
    unfold sieveClassPolar
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    calc
      x n ^ 2 = x n * (∑ i, c i * sieveClassPole Q (d i) n) := by
        change x n ^ 2 = x n * x n
        ring
      _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
  rw [hnorm]
  apply sum_congr rfl
  intro i _
  rw [sieveClassPolar_normalizedSieveProfile hd hinj]
  dsimp only [c]
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (sieveClassDensity_pos (hd i)).le]
  ring

theorem tendsto_normalizedSieveClassMass_sub_log
    {Q : Finset Nat.Primes} {d : ℕ} (hd : SieveSupported Q d) :
    Tendsto (fun M : ℕ => sieveClassMass Q d M / sieveClassDensity Q d - Real.log M)
      atTop (𝓝 (sieveEuler Q - Real.log d)) := by
  have h := ((tendsto_sieveClassMass_sub Q hd.pos).div_const (sieveClassDensity Q d)).add_const
    (sieveEuler Q - Real.log d)
  simp only [zero_div, zero_add] at h
  refine h.congr fun M => ?_
  field_simp [(sieveClassDensity_pos hd).ne']
  ring

theorem tendsto_normalizedSieveClassMass_div_log
    {Q : Finset Nat.Primes} {d : ℕ} (hd : SieveSupported Q d) :
    Tendsto (fun M : ℕ => (sieveClassMass Q d M / sieveClassDensity Q d) / Real.log M)
      atTop (𝓝 1) := by
  have h := (tendsto_sieveClassMass_div_log Q hd.pos).div_const (sieveClassDensity Q d)
  rw [div_self (sieveClassDensity_pos hd).ne'] at h
  exact h.congr fun M => by ring

/-- The polar counterterm differs from the matched ordinary norm by its affine class masses. -/
theorem tendsto_sieveCounterterm_sub_log_norm {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d) (b : ι → ℝ) :
    Tendsto (fun M : ℕ =>
      (sieveTensorCounterterm Q d M (normalizedSieveProfile Q d b) -
        Real.log M * ∑ n ∈ Icc 1 M, normalizedSieveProfile Q d b n ^ 2) / Real.log M)
      atTop (𝓝 (∑ i, b i ^ 2 * (sieveEuler Q - Real.log (d i)))) := by
  have h := tendsto_finsetSum univ fun i _ =>
    ((tendsto_normalizedSieveClassMass_div_log (hd i)).mul
      (tendsto_normalizedSieveClassMass_sub_log (hd i))).const_mul (b i ^ 2)
  simp only [one_mul] at h
  refine h.congr fun M => ?_
  rw [sieveTensorCounterterm_normalizedSieveProfile hd hinj,
    sum_normalizedSieveProfile_sq hd hinj, mul_sum, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro i _
  ring

/-- The actual horizon defect is the negative matched class quadratic form. -/
theorem tendsto_sieveProfile_matched_defect {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d) (b : ι → ℝ) :
    Tendsto (fun M : ℕ =>
      (primeBilinear M (normalizedSieveProfile Q d b) (normalizedSieveProfile Q d b) -
        Real.log M * ∑ n ∈ Icc 1 M, normalizedSieveProfile Q d b n ^ 2) / Real.log M)
      atTop (𝓝 (-(∑ i, (sieveEuler Q + Real.log (d i)) * b i ^ 2) +
        ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i) (d j))) := by
  have h := (tendsto_sieveProfile_finitePart hd hinj b).add
    (tendsto_sieveCounterterm_sub_log_norm hd hinj b)
  have hvalue :
      (-2 * sieveEuler Q * ∑ i, b i ^ 2 +
        ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i) (d j)) +
        (∑ i, b i ^ 2 * (sieveEuler Q - Real.log (d i))) =
      -(∑ i, (sieveEuler Q + Real.log (d i)) * b i ^ 2) +
        ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i) (d j) := by
    rw [mul_sum, ← sum_neg_distrib]
    have hs : (∑ i, -2 * sieveEuler Q * b i ^ 2) +
        (∑ i, b i ^ 2 * (sieveEuler Q - Real.log (d i))) =
        ∑ i, -((sieveEuler Q + Real.log (d i)) * b i ^ 2) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    linear_combination hs
  rw [hvalue] at h
  exact h.congr fun M => by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
