import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ResiduePatternGaugesAreMatchedByTheirMean

/-!
# Actual residue-prime readings on multiplicative windows

Every real residue pattern has a Mertens finite part. Subtracting two
linearly growing endpoints cancels that constant and leaves exactly its
unit mean times the logarithmic window length, with all prime powers kept.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory

/-- The literal von Mangoldt reading of a real residue pattern. -/
def residuePrimeReading (q : ℕ) (F : ZMod q → ℝ) (Y : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 Y, F (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℝ) / k

/-- Its finite part includes the convergent non-unit prime-power classes. -/
def residuePrimeFinitePart (q : ℕ) [NeZero q] (F : ZMod q → ℝ) : ℝ :=
  (∑ u : (ZMod q)ˣ, F u * classMertensConstant q u) +
    ∑ a ∈ univ.filter (fun a : ZMod q => ¬ IsUnit a),
      F a * ⨆ Y, classMertensSum q a Y

private theorem residuePrimeReading_eq_classes {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (Y : ℕ) :
    residuePrimeReading q F Y = ∑ a : ZMod q, F a * classMertensSum q a Y := by
  symm
  simp only [classMertensSum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_univ, if_true]
  ring

/-- Every actual residue pattern has a finite part, without a sign or
multiplicativity restriction on the pattern. -/
theorem tendsto_residuePrimeReading_sub_log {q : ℕ} [NeZero q] (F : ZMod q → ℝ) :
    Tendsto (fun Y : ℕ => residuePrimeReading q F Y - primeClassKappa q F * Real.log Y)
      atTop (𝓝 (residuePrimeFinitePart q F)) := by
  have hU : Tendsto (fun Y : ℕ => ∑ u : (ZMod q)ˣ,
      F u * (classMertensSum q u Y - Real.log Y / q.totient)) atTop
      (𝓝 (∑ u : (ZMod q)ˣ, F u * classMertensConstant q u)) :=
    tendsto_finsetSum _ fun u _ => (tendsto_classMertensSum_sub u.isUnit).const_mul _
  have hN : Tendsto (fun Y : ℕ =>
      ∑ a ∈ univ.filter (fun a : ZMod q => ¬ IsUnit a), F a * classMertensSum q a Y)
      atTop (𝓝 (∑ a ∈ univ.filter (fun a : ZMod q => ¬ IsUnit a),
        F a * ⨆ Y, classMertensSum q a Y)) :=
    tendsto_finsetSum _ fun a ha =>
      (tendsto_classMertensSum_of_not_isUnit (mem_filter.mp ha).2).const_mul _
  refine (hU.add hN).congr fun Y => ?_
  have hsplit : (∑ u : (ZMod q)ˣ,
      F u * (classMertensSum q u Y - Real.log Y / q.totient)) =
      (∑ u : (ZMod q)ˣ, F u * classMertensSum q u Y) -
        primeClassKappa q F * Real.log Y := by
    rw [primeClassKappa, sum_div, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun u _ => by ring
  rw [hsplit, residuePrimeReading_eq_classes, sum_zmod_eq_units_add]
  ring

/-- The actual reading between two multiplicatively scaled integer endpoints. -/
def residuePrimeWindow (q : ℕ) (F : ZMod q → ℝ) (A B N : ℕ) : ℝ :=
  ∑ k ∈ Ioc (A * N) (B * N), F (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℝ) / k

private theorem residuePrimeWindow_eq_sub {q A B : ℕ} (F : ZMod q → ℝ)
    (hAB : A ≤ B) (N : ℕ) :
    residuePrimeWindow q F A B N =
      residuePrimeReading q F (B * N) - residuePrimeReading q F (A * N) := by
  have hAN : A * N ≤ B * N := Nat.mul_le_mul_right N hAB
  have hset : Icc 1 (B * N) = Icc 1 (A * N) ∪ Ioc (A * N) (B * N) := by
    ext k
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 (A * N)) (Ioc (A * N) (B * N)) := by
    rw [disjoint_left]
    intro k hk hl
    exact (not_lt_of_ge (mem_Icc.mp hk).2) (mem_Ioc.mp hl).1
  have hsum := sum_union hdisj
    (f := fun k : ℕ => F (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℝ) / k)
  rw [← hset] at hsum
  change residuePrimeReading q F (B * N) =
    residuePrimeReading q F (A * N) + residuePrimeWindow q F A B N at hsum
  linarith only [hsum]

private theorem tendsto_mul_nat_atTop {A : ℕ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => A * N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [eventually_ge_atTop K] with N hN
  exact hN.trans (by simpa only [Nat.succ_eq_add_one, zero_add, one_mul] using
    Nat.mul_le_mul_right N (Nat.succ_le_of_lt hA))

/-- On every fixed multiplicative window, the literal prime reading tends to
the unit mean times its logarithmic length. No finite-part constant remains. -/
theorem tendsto_residuePrimeWindow {q : ℕ} [NeZero q] (F : ZMod q → ℝ)
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    Tendsto (residuePrimeWindow q F A B) atTop
      (𝓝 (primeClassKappa q F * (Real.log B - Real.log A))) := by
  have hB : 0 < B := hA.trans_le hAB
  have hLA := (tendsto_residuePrimeReading_sub_log F).comp (tendsto_mul_nat_atTop hA)
  have hLB := (tendsto_residuePrimeReading_sub_log F).comp (tendsto_mul_nat_atTop hB)
  have hlim := (hLB.sub hLA).add_const (primeClassKappa q F * (Real.log B - Real.log A))
  simp only [sub_self, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogA : Real.log (A * N : ℕ) = Real.log A + Real.log N := by
    rw [Nat.cast_mul, Real.log_mul hA0.ne' hN0.ne']
  have hlogB : Real.log (B * N : ℕ) = Real.log B + Real.log N := by
    rw [Nat.cast_mul, Real.log_mul hB0.ne' hN0.ne']
  dsimp only [Function.comp_def]
  rw [residuePrimeWindow_eq_sub F hAB N, hlogA, hlogB]
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_residuePrimeReading_sub_log
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_residuePrimeWindow
