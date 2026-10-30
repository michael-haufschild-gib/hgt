import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheTowerDeficit
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicSieveMassIsControlledByItsEulerCorrection

/-!
# A uniform Hodge index for the matched prime form

The spectral gap below the pole makes the matched prime form negative on its polar
hyperplane, uniformly over every finite family of vectors. Every finite sieve therefore
inherits at most one positive direction, even when the sieve grows with the horizon.
The full sieve partition contains the pole and has exactly one positive direction.
-/

noncomputable section

open Finset Matrix

universe u

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι]

/-- The prime Gram of a finite family, matched against a scalar Euclidean counterterm. -/
def matchedPrimeProfileGram (N : ℕ) (c : ℝ) (x : ι → ℕ → ℝ) : Matrix ι ι ℝ :=
  fun i j => primeBilinear N (x i) (x j) - c * ∑ n ∈ Icc 1 N, x i n * x j n

omit [Fintype ι] in
theorem matchedPrimeProfileGram_isSymm (N : ℕ) (c : ℝ) (x : ι → ℕ → ℝ) :
    (matchedPrimeProfileGram N c x).IsSymm := by
  ext i j
  simp only [transpose_apply, matchedPrimeProfileGram, primeBilinear_comm N (x j)]
  congr 2
  exact sum_congr rfl fun n _ => mul_comm _ _

/-- The Gram is the actual matched prime form on the synthesized vector. -/
theorem qf_matchedPrimeProfileGram (N : ℕ) (c : ℝ) (x : ι → ℕ → ℝ) (a : ι → ℝ) :
    qf (matchedPrimeProfileGram N c x) a =
      atomicWeilForm N (fun n => ∑ i, a i * x i n) -
        c * ∑ n ∈ Icc 1 N, (∑ i, a i * x i n) ^ 2 := by
  have hP : atomicWeilForm N (fun n => ∑ i, a i * x i n) =
      ∑ i, ∑ j, a i * a j * primeBilinear N (x i) (x j) := by
    rw [atomicWeilForm_eq_primeBilinear, primeBilinear_fintype_sum_left]
    refine sum_congr rfl fun i _ => ?_
    rw [primeBilinear_comm, primeBilinear_fintype_sum_left, mul_sum]
    exact sum_congr rfl fun j _ => by rw [primeBilinear_comm]; ring
  have hS : (∑ i, ∑ j, a i * a j * ∑ n ∈ Icc 1 N, x i n * x j n) =
      ∑ n ∈ Icc 1 N, (∑ i, a i * x i n) ^ 2 := by
    simp_rw [mul_sum]
    rw [show (∑ i, ∑ j, ∑ n ∈ Icc 1 N, a i * a j * (x i n * x j n)) =
        ∑ n ∈ Icc 1 N, ∑ i, ∑ j, a i * a j * (x i n * x j n) by
      calc
        _ = ∑ i, ∑ n ∈ Icc 1 N, ∑ j, a i * a j * (x i n * x j n) :=
          sum_congr rfl fun i _ => sum_comm
        _ = _ := sum_comm]
    refine sum_congr rfl fun n _ => ?_
    rw [sq, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [hP, ← hS]
  change (∑ i, a i * ∑ j, (primeBilinear N (x i) (x j) -
    c * ∑ n ∈ Icc 1 N, x i n * x j n) * a j) = _
  calc
    _ = ∑ i, ∑ j, (a i * a j * primeBilinear N (x i) (x j) -
        c * (a i * a j * ∑ n ∈ Icc 1 N, x i n * x j n)) := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    _ = _ := by simp only [sum_sub_distrib, mul_sum]

theorem polarFunctional_profile (N : ℕ) (x : ι → ℕ → ℝ) (a : ι → ℝ) :
    polarFunctional N (fun n => ∑ i, a i * x i n) =
      ∑ i, a i * polarFunctional N (x i) := by
  unfold polarFunctional
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun n _ => by ring

/-- One horizon works for every finite family, hence for arbitrarily growing finite sieves. -/
theorem eventually_isHyperbolic_matchedPrimeProfileGram {η : ℝ}
    (hη : η < 2 * Real.log 2) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ (κ : Type u) [Fintype κ] (x : κ → ℕ → ℝ),
      IsHyperbolic (matchedPrimeProfileGram N
        (Real.log N - Real.eulerMascheroniConstant - η) x) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_le_two_log_two
    (show 0 < (2 * Real.log 2 - η) / 2 by linarith)
  refine ⟨N₀, fun N hN κ _ x => isHyperbolic_of_nonpos_on_ker
    (matchedPrimeProfileGram_isSymm N _ x)
    (dotLeft (fun i => polarFunctional N (x i))) ?_⟩
  intro a ha
  have hpolar : polarFunctional N (fun n => ∑ i, a i * x i n) = 0 := by
    rw [polarFunctional_profile]
    change (∑ i, polarFunctional N (x i) * a i) = 0 at ha
    simpa only [mul_comm] using ha
  have hzero : ∑ n ∈ Icc 1 N, (∑ i, a i * x i n) / Real.sqrt n = 0 := by
    simpa only [polarFunctional, poleVector, mul_one_div] using hpolar
  have hbound := hN₀ N hN (fun n => ∑ i, a i * x i n) hzero
  have hmass : 0 ≤ ∑ n ∈ Icc 1 N, (∑ i, a i * x i n) ^ 2 :=
    sum_nonneg fun n _ => sq_nonneg _
  rw [qf_matchedPrimeProfileGram]
  nlinarith

/-- The pole carries a strictly positive square for every positive matching offset. -/
theorem eventually_matchedPrime_pole_pos {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      0 < atomicWeilForm N (truncPole N) -
        (Real.log N - Real.eulerMascheroniConstant - η) *
          ∑ n ∈ Icc 1 N, truncPole N n ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_truncPole_ge
    (show 0 < η / 2 by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hmass : 0 < ∑ n ∈ Icc 1 N, truncPole N n ^ 2 := by
    have h := single_le_sum (f := fun n => truncPole N n ^ 2)
      (fun n _ => sq_nonneg _) (mem_Icc.mpr ⟨le_rfl, hN1⟩)
    have he : truncPole N 1 = 1 := by simp only [truncPole, if_pos hN1, poleVector,
      Nat.cast_one, Real.sqrt_one, div_one]
    rw [he, one_pow] at h
    exact one_pos.trans_le h
  have hbound := hN₀ N ((le_max_left _ _).trans hN)
  nlinarith [mul_pos hη hmass]

/-- The finite-sieve class partition sums to the pole on the actual horizon. -/
theorem sum_sieveClassPrefix_pole (Q : Finset Nat.Primes) {N n : ℕ}
    (hn : n ∈ Icc 1 N) :
    (∑ a : sieveClassPrefix Q N, sieveClassPole Q (a.1 : ℕ) n) = truncPole N n := by
  classical
  obtain ⟨a, b, hb, hcop, hab⟩ := exists_sieveFactorization Q (mem_Icc.mp hn).1
  have haN : (a : ℕ) ≤ N :=
    (Nat.le_of_dvd (mem_Icc.mp hn).1 ⟨b, hab.symm⟩).trans (mem_Icc.mp hn).2
  let a' : sieveClassPrefix Q N := ⟨a, (mem_sieveClassPrefix Q N a).mpr haN⟩
  have hapole : sieveClassPole Q (a : ℕ) n = poleVector n := by
    rw [← hab, sieveClassPole]
    exact if_pos ⟨dvd_mul_right _ _, by rwa [Nat.mul_div_cancel_left b a.property.pos]⟩
  have hpn : poleVector n ≠ 0 := by
    unfold poleVector
    exact one_div_ne_zero (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)).ne'
  rw [sum_eq_single a']
  · change sieveClassPole Q (a : ℕ) n = _
    rw [hapole, truncPole, if_pos (mem_Icc.mp hn).2]
  · intro d _ hda
    have hne : (d.1 : ℕ) ≠ (a : ℕ) := fun h => hda (Subtype.ext (Subtype.ext h))
    have h := sieveClassPole_mul_eq_zero d.1.property a.property hne n
    rw [hapole] at h
    exact (mul_eq_zero.mp h).resolve_right hpn
  · simp

/-- The matched prime Gram on every class present at the horizon. -/
def sieveHodgeGram (Q : Finset Nat.Primes) (N : ℕ) (η : ℝ) :
    Matrix (sieveClassPrefix Q N) (sieveClassPrefix Q N) ℝ :=
  matchedPrimeProfileGram N (Real.log N - Real.eulerMascheroniConstant - η)
    (fun a => sieveClassPole Q (a.1 : ℕ))

theorem qf_sieveHodgeGram_one (Q : Finset Nat.Primes) (N : ℕ) (η : ℝ) :
    qf (sieveHodgeGram Q N η) (fun _ => 1) =
      atomicWeilForm N (truncPole N) -
        (Real.log N - Real.eulerMascheroniConstant - η) *
          ∑ n ∈ Icc 1 N, truncPole N n ^ 2 := by
  rw [sieveHodgeGram, qf_matchedPrimeProfileGram]
  simp only [one_mul]
  congr 1
  · rw [atomicWeilForm_eq_primeBilinear, atomicWeilForm_eq_primeBilinear]
    unfold primeBilinear
    exact sum_congr rfl fun m hm => sum_congr rfl fun n hn => by
      dsimp only
      rw [sum_sieveClassPrefix_pole Q hm, sum_sieveClassPrefix_pole Q hn]
  · congr 1
    exact sum_congr rfl fun n hn => by rw [sum_sieveClassPrefix_pole Q hn]

/-- Every finite sieve has exactly one positive direction, with a horizon independent of
the sieve. The all-ones class vector is the shared pole. -/
theorem eventually_sieveHodgeGram_one_positive_direction {η : ℝ} (hη : 0 < η)
    (hgap : η < 2 * Real.log 2) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ Q : Finset Nat.Primes,
      IsHyperbolic (sieveHodgeGram Q N η) ∧
        0 < qf (sieveHodgeGram Q N η) (fun _ => 1) := by
  obtain ⟨N₁, hN₁⟩ := eventually_isHyperbolic_matchedPrimeProfileGram.{0} hgap
  obtain ⟨N₂, hN₂⟩ := eventually_matchedPrime_pole_pos hη
  refine ⟨max N₁ N₂, fun N hN Q => ⟨?_, ?_⟩⟩
  · exact hN₁ N ((le_max_left _ _).trans hN) (sieveClassPrefix Q N)
      (fun a => sieveClassPole Q (a.1 : ℕ))
  · rw [qf_sieveHodgeGram_one]
    exact hN₂ N ((le_max_right _ _).trans hN)

#print axioms eventually_isHyperbolic_matchedPrimeProfileGram
#print axioms eventually_sieveHodgeGram_one_positive_direction

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
