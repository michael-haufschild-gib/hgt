import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasTheTowerFinitePart

/-!
# Hecke covariance for every prime of a finite sieve

Multiplication by a supported order moves each class to another class of the same
sieve. Its pole coordinate scales by the inverse square root of the degree and
its density by the inverse degree. These factors cancel in the tensor polar
counterterm, so the renormalized prime form has no Hecke anomaly.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.ArithmeticElectrostatics

theorem SieveSupported.prime {Q : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∈ Q) :
    SieveSupported Q (p : ℕ) := by
  refine ⟨1, ?_⟩
  rw [pow_one, sievePrimorial]
  exact dvd_prod_of_mem (fun q : Nat.Primes => (q : ℕ)) hp

/-- Common dilation scales the class pole vector by the inverse square root. -/
theorem sieveClassPole_mul_left {t : ℕ} (ht : 0 < t)
    (Q : Finset Nat.Primes) (d n : ℕ) :
    sieveClassPole Q (t * d) (t * n) = poleVector t * sieveClassPole Q d n := by
  simp only [sieveClassPole, Nat.mul_dvd_mul_iff_left ht, Nat.mul_div_mul_left _ _ ht]
  split_ifs
  · exact poleVector_mul_nat t n
  · ring

/-- The class pole coordinate has Hecke weight minus one half. -/
theorem sieveClassPolar_heckeShift {t : ℕ} (ht : 0 < t)
    (Q : Finset Nat.Primes) (d M : ℕ) (x : ℕ → ℝ) :
    sieveClassPolar Q (t * d) (t * M) (heckeShift t x) =
      sieveClassPolar Q d M x / Real.sqrt t := by
  have hterm : ∀ n : ℕ,
      heckeShift t x n * sieveClassPole Q (t * d) n =
        if t ∣ n then poleVector t * (x (n / t) * sieveClassPole Q d (n / t)) else 0 := by
    intro n
    by_cases htn : t ∣ n
    · obtain ⟨k, rfl⟩ := htn
      rw [heckeShift, if_pos (dvd_mul_right t k), if_pos (dvd_mul_right t k),
        Nat.mul_div_cancel_left k ht, sieveClassPole_mul_left ht]
      ring
    · simp [heckeShift, htn]
  rw [sieveClassPolar, sum_congr rfl fun n _ => hterm n,
    sum_Icc_mul_dvd ht M (fun n => poleVector t * (x n * sieveClassPole Q d n)), ← mul_sum]
  simp only [sieveClassPolar, poleVector]
  ring

/-- The class density has Hecke weight minus one. -/
theorem sieveClassDensity_mul (Q : Finset Nat.Primes) (t d : ℕ) :
    sieveClassDensity Q (t * d) = sieveClassDensity Q d / t := by
  simp only [sieveClassDensity, Nat.cast_mul]
  ring

/-- Every supported Hecke correspondence preserves the tensor polar counterterm. -/
theorem sieveTensorCounterterm_heckeShift {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ} {t : ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (ht : SieveSupported Q t)
    (M : ℕ) (x : ℕ → ℝ) :
    sieveTensorCounterterm Q (fun i => t * d i) (t * M) (heckeShift t x) =
      sieveTensorCounterterm Q d M x := by
  unfold sieveTensorCounterterm
  refine sum_congr rfl fun i _ => ?_
  rw [sieveClassPolar_heckeShift ht.pos, sieveClassDensity_mul, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg t)]
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.pos.ne'
  have hδ : sieveClassDensity Q (d i) ≠ 0 := (sieveClassDensity_pos (hd i)).ne'
  field_simp

/-- The renormalized prime form is exactly Hecke covariant, for arbitrary signs. -/
theorem sieveFinitePart_heckeShift {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ} {t : ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (ht : SieveSupported Q t)
    (M : ℕ) (x : ℕ → ℝ) :
    primeBilinear (t * M) (heckeShift t x) (heckeShift t x) -
        sieveTensorCounterterm Q (fun i => t * d i) (t * M) (heckeShift t x) =
      primeBilinear M x x - sieveTensorCounterterm Q d M x := by
  change atomicWeilForm (t * M) (heckeShift t x) -
      sieveTensorCounterterm Q (fun i => t * d i) (t * M) (heckeShift t x) =
    atomicWeilForm M x - sieveTensorCounterterm Q d M x
  rw [atomicWeilForm_heckeShift ht.pos, sieveTensorCounterterm_heckeShift hd ht]

/-- The survival space consists exactly of the profiles neutral in every class. -/
theorem sieveTensorCounterterm_eq_zero_iff {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (M : ℕ) (x : ℕ → ℝ) :
    sieveTensorCounterterm Q d M x = 0 ↔ ∀ i, sieveClassPolar Q (d i) M x = 0 := by
  unfold sieveTensorCounterterm
  rw [sum_eq_zero_iff_of_nonneg (fun i _ =>
    div_nonneg (sq_nonneg _) (sieveClassDensity_pos (hd i)).le)]
  constructor
  · intro h i
    have hsquare : sieveClassPolar Q (d i) M x ^ 2 = 0 :=
      (div_eq_zero_iff.mp (h i (mem_univ i))).resolve_right (sieveClassDensity_pos (hd i)).ne'
    nlinarith only [hsquare]
  · intro h i _
    rw [h i]
    simp

/-- A class has positive mass once its first supported order is inside the horizon. -/
theorem sieveClassMass_pos {Q : Finset Nat.Primes} {d M : ℕ}
    (hd : 0 < d) (hdM : d ≤ M) : 0 < sieveClassMass Q d M := by
  have hq : 1 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdM)
  have hmem : 1 ∈ sieveUnits Q (M / d) := by simp [sieveUnits, hq]
  have hmass : (1 : ℝ) ≤ sievedHarmonic Q (M / d) := by
    change 1 ≤ ∑ n ∈ sieveUnits Q (M / d), 1 / (n : ℝ)
    have h := single_le_sum (fun n (_ : n ∈ sieveUnits Q (M / d)) =>
      show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity) hmem
    simpa only [Nat.cast_one, div_one] using h
  exact div_pos (zero_lt_one.trans_le hmass) (by exact_mod_cast hd)

/-- Once all selected orders are visible, their polar coordinates are independent:
every finite list of class charges is realized by a profile. -/
theorem sieveClassPolar_surjective {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d)
    {M : ℕ} (hM : ∀ i, d i ≤ M) :
    Function.Surjective (fun x : ℕ → ℝ => fun i => sieveClassPolar Q (d i) M x) := by
  intro u
  let b : ι → ℝ := fun i =>
    u i * Real.sqrt (sieveClassDensity Q (d i)) / sieveClassMass Q (d i) M
  refine ⟨normalizedSieveProfile Q d b, ?_⟩
  funext i
  change sieveClassPolar Q (d i) M (normalizedSieveProfile Q d b) = u i
  rw [sieveClassPolar_normalizedSieveProfile hd hinj]
  have hm : sieveClassMass Q (d i) M ≠ 0 := (sieveClassMass_pos (hd i).pos (hM i)).ne'
  have hs : Real.sqrt (sieveClassDensity Q (d i)) ≠ 0 :=
    (Real.sqrt_pos.mpr (sieveClassDensity_pos (hd i))).ne'
  dsimp only [b]
  field_simp [hm, hs]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
