import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveClassesHaveExactTruncatedGrams

/-!
# The finite-sieve tensor law on signed step profiles

Each class may carry finitely many independently truncated pole profiles.
The exact polar counterterm removes the quadratic harmonic divergence.
The remaining form is the shared Euler scalar on ordinary mass plus the
transverse tower interaction at the common unit cutoffs. A uniform boundary
estimate controls the remainder without restricting coefficient signs.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-- The exact transverse tower interaction at two class cutoffs. -/
def sieveTruncTowerKernel (Q : Finset Nat.Primes) (d e A B : ℕ) : ℝ :=
  poleVector d * poleVector e * weilPrimeKernel d e *
    sievedHarmonic Q (min (A / d) (B / e))

/-- A finite signed step profile, with a class label and cutoff for each generator. -/
def sieveStepProfile {ι κ : Type*} [Fintype κ]
    (Q : Finset Nat.Primes) (d : ι → ℕ) (a : κ → ι)
    (M : κ → ℕ) (c : κ → ℝ) (n : ℕ) : ℝ :=
  ∑ r, c r * sieveTruncPole Q (d (a r)) (M r) n

private theorem abs_classCombination_le {κ : Type*} [Fintype κ]
    (c : κ → ℝ) (E : κ → κ → ℝ) {K : ℝ} (hE : ∀ r s, |E r s| ≤ K) :
    |∑ r, ∑ s, c r * c s * E r s| ≤ K * (∑ r, |c r|) ^ 2 := by
  calc
    |∑ r, ∑ s, c r * c s * E r s| ≤ ∑ r, ∑ s, |c r| * |c s| * K := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hE r s) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = K * (∑ r, |c r|) ^ 2 := by
      rw [sq, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun s _ => by ring

theorem primeBilinear_sieveStepProfile {ι κ : Type*} [Fintype κ]
    (Q : Finset Nat.Primes) (d : ι → ℕ) (a : κ → ι)
    (M : κ → ℕ) (c : κ → ℝ) (N : ℕ) :
    primeBilinear N (sieveStepProfile Q d a M c) (sieveStepProfile Q d a M c) =
      ∑ r, ∑ s, c r * c s *
        primeBilinear N (sieveTruncPole Q (d (a r)) (M r)) (sieveTruncPole Q (d (a s)) (M s)) := by
  have hlinear : ∀ y, primeBilinear N (sieveStepProfile Q d a M c) y =
      ∑ r, c r * primeBilinear N (sieveTruncPole Q (d (a r)) (M r)) y := fun y =>
    primeBilinear_fintype_sum_left N c (fun r => sieveTruncPole Q (d (a r)) (M r)) y
  rw [hlinear]
  refine sum_congr rfl fun r _ => ?_
  rw [primeBilinear_comm, hlinear, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [primeBilinear_comm]
  ring

theorem sum_sieveStepProfile_sq {ι κ : Type*} [Fintype κ]
    {Q : Finset Nat.Primes} {d : ι → ℕ} (hd : ∀ i, SieveSupported Q (d i))
    (a : κ → ι) (M : κ → ℕ) (c : κ → ℝ) {N : ℕ} (hM : ∀ r, M r ≤ N) :
    (∑ n ∈ Icc 1 N, sieveStepProfile Q d a M c n ^ 2) =
      ∑ r, ∑ s, c r * c s *
        (if d (a r) = d (a s) then sieveClassMass Q (d (a r)) (min (M r) (M s)) else 0) := by
  classical
  simp only [sieveStepProfile, sq, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  calc
    (∑ n ∈ Icc 1 N,
      (c r * sieveTruncPole Q (d (a r)) (M r) n) *
        (c s * sieveTruncPole Q (d (a s)) (M s) n)) =
      c r * c s * (∑ n ∈ Icc 1 N,
        sieveTruncPole Q (d (a r)) (M r) n * sieveTruncPole Q (d (a s)) (M s) n) := by
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring
    _ = _ := by rw [sum_sieveTruncPole_mul_sieveTruncPole (hd _) (hd _) (hM r) (hM s)]

/-- The actual polar counterterm expands into the same-class mass products. -/
theorem sieveTensorCounterterm_sieveStepProfile {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Q : Finset Nat.Primes} {d : ι → ℕ} (hd : ∀ i, SieveSupported Q (d i))
    (hinj : Function.Injective d) (a : κ → ι) (M : κ → ℕ) (c : κ → ℝ)
    {N : ℕ} (hM : ∀ r, M r ≤ N) :
    sieveTensorCounterterm Q d N (sieveStepProfile Q d a M c) =
      ∑ r, ∑ s, c r * c s *
        (if d (a r) = d (a s) then
          sieveClassMass Q (d (a r)) (M r) * sieveClassMass Q (d (a s)) (M s) /
            sieveClassDensity Q (d (a r)) else 0) := by
  classical
  have hpolar : ∀ i, sieveClassPolar Q (d i) N (sieveStepProfile Q d a M c) =
      ∑ r, if a r = i then c r * sieveClassMass Q (d i) (M r) else 0 := by
    intro i
    change sieveClassPolar Q (d i) N (fun n =>
      ∑ r, c r * sieveTruncPole Q (d (a r)) (M r) n) = _
    rw [sieveClassPolar_fintype_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [sieveClassPolar_sieveTruncPole (hd i) (hd (a r)) (hM r)]
    by_cases ha : a r = i
    · rw [ha, if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => ha (hinj h).symm), if_neg ha, mul_zero]
  simp only [sieveTensorCounterterm, hpolar, sq, sum_mul_sum, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_eq_single (a r)]
  · rw [if_pos rfl]
    by_cases hrs : a r = a s
    · rw [if_pos (Eq.symm hrs), if_pos (congrArg d hrs), ← hrs]
      ring
    · rw [if_neg (Ne.symm hrs), if_neg (fun h => hrs (hinj h)), mul_zero, zero_div, mul_zero]
  · intro i _ hir
    rw [if_neg (Ne.symm hir), zero_mul, zero_div]
  · simp

/-- The tensor counterterm and the finite tower part have a uniform signed
step-profile remainder. The constant is independent of class orders, cutoffs,
and the number of generators; the displayed coefficient mass carries their cost. -/
theorem exists_sieveStepProfile_finitePart_bound (Q : Finset Nat.Primes)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ : Type*} [Fintype ι] [Fintype κ]
      (d : ι → ℕ), (∀ i, SieveSupported Q (d i)) → Function.Injective d →
      ∀ (a : κ → ι) (M : κ → ℕ) (c : κ → ℝ) (N : ℕ), (∀ r, M r ≤ N) →
      |primeBilinear N (sieveStepProfile Q d a M c) (sieveStepProfile Q d a M c) -
        sieveTensorCounterterm Q d N (sieveStepProfile Q d a M c) +
        2 * sieveEuler Q * (∑ n ∈ Icc 1 N, sieveStepProfile Q d a M c n ^ 2) -
        (∑ r, ∑ s, c r * c s * sieveTruncTowerKernel Q (d (a r)) (d (a s)) (M r) (M s))| ≤
          (η * harmonicSum N + C) * (∑ r, |c r|) ^ 2 := by
  classical
  obtain ⟨C, hC, hdiag⟩ := exists_sieveTruncPole_finitePart_bound Q hη
  refine ⟨C, hC, fun {ι κ} _ _ d hd hinj a M c N hM => ?_⟩
  let E : κ → κ → ℝ := fun r s =>
    primeBilinear N (sieveTruncPole Q (d (a r)) (M r)) (sieveTruncPole Q (d (a s)) (M s)) -
      (if d (a r) = d (a s) then
        sieveClassMass Q (d (a r)) (M r) * sieveClassMass Q (d (a s)) (M s) /
          sieveClassDensity Q (d (a r)) else 0) +
      2 * sieveEuler Q * (if d (a r) = d (a s) then
        sieveClassMass Q (d (a r)) (min (M r) (M s)) else 0) -
      sieveTruncTowerKernel Q (d (a r)) (d (a s)) (M r) (M s)
  have hentry : ∀ r s, |E r s| ≤ η * harmonicSum N + C := by
    intro r s
    dsimp only [E]
    by_cases hrs : d (a r) = d (a s)
    · simp only [← hrs, ↓reduceIte, sieveTruncTowerKernel, weilPrimeKernel_self,
        mul_zero, zero_mul, sub_zero]
      exact (hdiag (d (a r)) (hd _).pos (M r) (M s) N (hM r) (hM s)).trans
        (add_le_add (mul_le_mul_of_nonneg_left
          (harmonicSum_mono ((min_le_left _ _).trans (hM r))) hη.le) le_rfl)
    · rw [if_neg hrs, if_neg hrs, mul_zero, sub_zero, add_zero,
        primeBilinear_sieveTruncPole_cross (hd _) (hd _) hrs (hM r) (hM s)]
      simp only [sieveTruncTowerKernel, sub_self, abs_zero]
      exact add_nonneg (mul_nonneg hη.le (harmonicSum_nonneg N)) hC
  have hexpand : primeBilinear N (sieveStepProfile Q d a M c) (sieveStepProfile Q d a M c) -
      sieveTensorCounterterm Q d N (sieveStepProfile Q d a M c) +
      2 * sieveEuler Q * (∑ n ∈ Icc 1 N, sieveStepProfile Q d a M c n ^ 2) -
      (∑ r, ∑ s, c r * c s * sieveTruncTowerKernel Q (d (a r)) (d (a s)) (M r) (M s)) =
        ∑ r, ∑ s, c r * c s * E r s := by
    rw [primeBilinear_sieveStepProfile, sieveTensorCounterterm_sieveStepProfile hd hinj a M c hM,
      sum_sieveStepProfile_sq hd a M c hM, mul_sum,
      ← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun s _ => by dsimp only [E]; ring
  rw [hexpand]
  exact abs_classCombination_le c E hentry

/-- The horizon divergence on every finite class-wise step space is exactly the
tensor polar counterterm, with a harmonic-size remainder for arbitrary signs. -/
theorem exists_sieveStepProfile_tensor_bound {ι : Type*} [Fintype ι]
    (Q : Finset Nat.Primes) (d : ι → ℕ) (hd : ∀ i, SieveSupported Q (d i))
    (hinj : Function.Injective d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {κ : Type*} [Fintype κ]
      (a : κ → ι) (M : κ → ℕ) (c : κ → ℝ) (N : ℕ), (∀ r, M r ≤ N) →
      |primeBilinear N (sieveStepProfile Q d a M c) (sieveStepProfile Q d a M c) -
        sieveTensorCounterterm Q d N (sieveStepProfile Q d a M c)| ≤
          K * (harmonicSum N + 1) * (∑ r, |c r|) ^ 2 := by
  classical
  obtain ⟨C, hC, hdiag⟩ := exists_sieveTruncPole_finitePart_bound Q (by norm_num : (0 : ℝ) < 1)
  let T : ℝ := ∑ i, ∑ j, |poleVector (d i) * poleVector (d j) * weilPrimeKernel (d i) (d j)|
  have hT : 0 ≤ T := sum_nonneg fun i _ => sum_nonneg fun j _ => abs_nonneg _
  have hw : ∀ i j,
      |poleVector (d i) * poleVector (d j) * weilPrimeKernel (d i) (d j)| ≤ T := by
    intro i j
    exact (single_le_sum (fun k _ => abs_nonneg
      (poleVector (d i) * poleVector (d k) * weilPrimeKernel (d i) (d k))) (mem_univ j)).trans
      (single_le_sum (fun k _ => sum_nonneg fun l _ => abs_nonneg
        (poleVector (d k) * poleVector (d l) * weilPrimeKernel (d k) (d l))) (mem_univ i))
  let K : ℝ := 1 + C + 2 * |sieveEuler Q| + T
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hKdiag : 1 + 2 * |sieveEuler Q| ≤ K := by dsimp only [K]; linarith only [hC, hT]
  have hKC : C ≤ K := by dsimp only [K]; linarith only [abs_nonneg (sieveEuler Q), hT]
  have hKT : T ≤ K := by dsimp only [K]; linarith only [hC, abs_nonneg (sieveEuler Q)]
  have hentry : ∀ (i j : ι) (A B N : ℕ), A ≤ N → B ≤ N →
      |primeBilinear N (sieveTruncPole Q (d i) A) (sieveTruncPole Q (d j) B) -
        (if d i = d j then sieveClassMass Q (d i) A * sieveClassMass Q (d j) B /
          sieveClassDensity Q (d i) else 0)| ≤ K * (harmonicSum N + 1) := by
    intro i j A B N hAN hBN
    have hHN := harmonicSum_nonneg N
    by_cases hij : d i = d j
    · have hij' : i = j := hinj hij
      subst j
      rw [if_pos rfl]
      have hsmall :
          |primeBilinear N (sieveTruncPole Q (d i) A) (sieveTruncPole Q (d i) B) -
            sieveClassMass Q (d i) A * sieveClassMass Q (d i) B / sieveClassDensity Q (d i) +
            2 * sieveEuler Q * sieveClassMass Q (d i) (min A B)| ≤ harmonicSum N + C := by
        have hb := hdiag (d i) (hd i).pos A B N hAN hBN
        rw [one_mul] at hb
        exact hb.trans (add_le_add (harmonicSum_mono ((min_le_left A B).trans hAN)) le_rfl)
      have hmass : sieveClassMass Q (d i) (min A B) ≤ harmonicSum N :=
        (sieveClassMass_le_harmonicSum Q (hd i).pos _).trans
          (harmonicSum_mono ((min_le_left A B).trans hAN))
      have hEuler : |2 * sieveEuler Q * sieveClassMass Q (d i) (min A B)| ≤
          2 * |sieveEuler Q| * harmonicSum N := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sieveClassMass_nonneg Q _ _)]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left hmass (by positivity)
      calc
        |primeBilinear N (sieveTruncPole Q (d i) A) (sieveTruncPole Q (d i) B) -
            sieveClassMass Q (d i) A * sieveClassMass Q (d i) B / sieveClassDensity Q (d i)| =
          |(primeBilinear N (sieveTruncPole Q (d i) A) (sieveTruncPole Q (d i) B) -
            sieveClassMass Q (d i) A * sieveClassMass Q (d i) B / sieveClassDensity Q (d i) +
            2 * sieveEuler Q * sieveClassMass Q (d i) (min A B)) -
            2 * sieveEuler Q * sieveClassMass Q (d i) (min A B)| := by congr 1; ring
        _ ≤ harmonicSum N + C + 2 * |sieveEuler Q| * harmonicSum N :=
          (abs_sub _ _).trans (add_le_add hsmall hEuler)
        _ = (1 + 2 * |sieveEuler Q|) * harmonicSum N + C := by ring
        _ ≤ K * harmonicSum N + K := add_le_add
          (mul_le_mul_of_nonneg_right hKdiag hHN) hKC
        _ = K * (harmonicSum N + 1) := by ring
    · rw [if_neg hij, sub_zero,
        primeBilinear_sieveTruncPole_cross (hd i) (hd j) hij hAN hBN, abs_mul,
        abs_of_nonneg (sievedHarmonic_nonneg Q _)]
      have hmass : sievedHarmonic Q (min (A / d i) (B / d j)) ≤ harmonicSum N :=
        (sievedHarmonic_le_harmonicSum Q _).trans (harmonicSum_mono
          ((min_le_left _ _).trans ((Nat.div_le_self A (d i)).trans hAN)))
      calc
        |poleVector (d i) * poleVector (d j) * weilPrimeKernel (d i) (d j)| *
            sievedHarmonic Q (min (A / d i) (B / d j)) ≤ T * harmonicSum N :=
          mul_le_mul (hw i j) hmass (sievedHarmonic_nonneg Q _) hT
        _ ≤ K * harmonicSum N := mul_le_mul_of_nonneg_right hKT hHN
        _ ≤ K * (harmonicSum N + 1) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hK
  refine ⟨K, hK, fun {κ} _ a M c N hM => ?_⟩
  let E : κ → κ → ℝ := fun r s =>
    primeBilinear N (sieveTruncPole Q (d (a r)) (M r)) (sieveTruncPole Q (d (a s)) (M s)) -
      (if d (a r) = d (a s) then
        sieveClassMass Q (d (a r)) (M r) * sieveClassMass Q (d (a s)) (M s) /
          sieveClassDensity Q (d (a r)) else 0)
  have hexpand : primeBilinear N (sieveStepProfile Q d a M c) (sieveStepProfile Q d a M c) -
      sieveTensorCounterterm Q d N (sieveStepProfile Q d a M c) =
        ∑ r, ∑ s, c r * c s * E r s := by
    rw [primeBilinear_sieveStepProfile, sieveTensorCounterterm_sieveStepProfile hd hinj a M c hM,
      ← sum_sub_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun s _ => by dsimp only [E]; ring
  rw [hexpand]
  exact abs_classCombination_le c E fun r s => hentry (a r) (a s) (M r) (M s) N (hM r) (hM s)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
