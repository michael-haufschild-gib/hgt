/-
# Adjacent direct-dilation differences are differentially free

The coefficient stream

`c_m(n) = [n is a perfect m-th power] - [n is a perfect (m+1)-st power]`

is supported on integers with at least `m` prime factors counted with multiplicity, and its lowest
grade is the pure prime ray: `Ω n = m` forces `n = q^m` and `c_m(q^m) = 1`.  That is exactly the
input of the Ω-leading-echelon law, so assigning level `m` to `c_m` and level one to the zeta
stream makes every finite jet rectangle of the unified family algebraically independent, and the
finite-abscissa transfer carries the conclusion to the actual upper-end meromorphic carriers.
-/
import GaloisForLFunctions.RHTower.HighExponentShellHypertranscendence

open scoped BigOperators ArithmeticFunction.Omega Differential
  UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace RHTower.AdjacentDilation

open ArithmeticFunction
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open RHTower

noncomputable section

open Classical in
/-- The adjacent direct-dilation coefficient: the indicator of perfect `m`-th powers minus the
indicator of perfect `(m+1)`-st powers. -/
def adjacentDilationCoeff (m : ℕ) : ArithmeticFunction ℂ where
  toFun n :=
    if n = 0 then 0
    else ((if ∃ a : ℕ, n = a ^ m then (1 : ℂ) else 0)
      - (if ∃ b : ℕ, n = b ^ (m + 1) then (1 : ℂ) else 0))
  map_zero' := by simp

open Classical in
theorem adjacentDilationCoeff_apply {m n : ℕ} (hn : n ≠ 0) :
    adjacentDilationCoeff m n
      = ((if ∃ a : ℕ, n = a ^ m then (1 : ℂ) else 0)
        - (if ∃ b : ℕ, n = b ^ (m + 1) then (1 : ℂ) else 0)) := by
  simp only [adjacentDilationCoeff, ArithmeticFunction.coe_mk, if_neg hn]

theorem adjacentDilationCoeff_eq_zero_of_both {m n : ℕ}
    (ha : ∃ a : ℕ, n = a ^ m) (hb : ∃ b : ℕ, n = b ^ (m + 1)) :
    adjacentDilationCoeff m n = 0 := by
  classical
  by_cases hn : n = 0
  · simp [adjacentDilationCoeff, hn]
  · rw [adjacentDilationCoeff_apply hn, if_pos ha, if_pos hb, sub_self]

/-- A nonzero adjacent-dilation coefficient has at least `m` prime factors. -/
theorem adjacentDilationCoeff_cardFactors_lower {m n : ℕ} (hm : 0 < m)
    (h : adjacentDilationCoeff m n ≠ 0) : m ≤ Ω n := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    exact h (by simp [adjacentDilationCoeff, hn])
  have hn1 : n ≠ 1 := by
    intro hn1
    exact h (adjacentDilationCoeff_eq_zero_of_both ⟨1, by simp [hn1]⟩ ⟨1, by simp [hn1]⟩)
  rw [adjacentDilationCoeff_apply hn] at h
  by_cases ha : ∃ a : ℕ, n = a ^ m
  · obtain ⟨a, rfl⟩ := ha
    have ha0 : a ≠ 0 := by
      intro h0
      exact hn (by simp [h0, hm.ne'])
    have ha1 : a ≠ 1 := by
      intro h1
      exact hn1 (by simp [h1])
    have hΩa : 1 ≤ Ω a := by
      rcases Nat.eq_zero_or_pos (Ω a) with h0 | hpos
      · rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h | h
        · exact absurd h ha0
        · exact absurd h ha1
      · exact hpos
    rw [cardFactors_pow]
    nlinarith
  · rw [if_neg ha, zero_sub, neg_ne_zero] at h
    by_cases hb : ∃ b : ℕ, n = b ^ (m + 1)
    · obtain ⟨b, rfl⟩ := hb
      have hb0 : b ≠ 0 := by
        intro h0
        exact hn (by simp [h0])
      have hb1 : b ≠ 1 := by
        intro h1
        exact hn1 (by simp [h1])
      have hΩb : 1 ≤ Ω b := by
        rcases Nat.eq_zero_or_pos (Ω b) with h0 | hpos
        · rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h' | h'
          · exact absurd h' hb0
          · exact absurd h' hb1
        · exact hpos
      rw [cardFactors_pow]
      nlinarith
    · rw [if_neg hb] at h
      exact absurd rfl h

/-- Equality in the grade bound characterizes a pure prime power. -/
theorem adjacentDilationCoeff_eq_prime_pow_of_cardFactors_eq {m n : ℕ} (hm : 0 < m)
    (h : adjacentDilationCoeff m n ≠ 0) (hΩ : Ω n = m) :
    ∃ q : Nat.Primes, n = (q : ℕ) ^ m := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    exact h (by simp [adjacentDilationCoeff, hn])
  have hn1 : n ≠ 1 := by
    intro hn1
    exact h (adjacentDilationCoeff_eq_zero_of_both ⟨1, by simp [hn1]⟩ ⟨1, by simp [hn1]⟩)
  by_cases ha : ∃ a : ℕ, n = a ^ m
  · obtain ⟨a, rfl⟩ := ha
    have ha0 : a ≠ 0 := by
      intro h0
      exact hn (by simp [h0, hm.ne'])
    have ha1 : a ≠ 1 := by
      intro h1
      exact hn1 (by simp [h1])
    rw [cardFactors_pow] at hΩ
    have hΩa : Ω a = 1 := by
      rcases Nat.eq_zero_or_pos (Ω a) with h0 | hpos
      · rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h' | h'
        · exact absurd h' ha0
        · exact absurd h' ha1
      · nlinarith
    exact ⟨⟨a, cardFactors_eq_one_iff_prime.mp hΩa⟩, rfl⟩
  · exfalso
    rw [adjacentDilationCoeff_apply hn, if_neg ha, zero_sub, neg_ne_zero] at h
    by_cases hb : ∃ b : ℕ, n = b ^ (m + 1)
    · obtain ⟨b, rfl⟩ := hb
      have hb0 : b ≠ 0 := by
        intro h0
        exact hn (by simp [h0])
      have hb1 : b ≠ 1 := by
        intro h1
        exact hn1 (by simp [h1])
      have hΩb : 1 ≤ Ω b := by
        rcases Nat.eq_zero_or_pos (Ω b) with h0 | hpos
        · rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h' | h'
          · exact absurd h' hb0
          · exact absurd h' hb1
        · exact hpos
      rw [cardFactors_pow] at hΩ
      nlinarith
    · rw [if_neg hb] at h
      exact absurd rfl h

/-- The coefficient at a pure prime power of the leading exponent is one. -/
theorem adjacentDilationCoeff_prime_pow {m : ℕ} (hm : 0 < m) (q : Nat.Primes) :
    adjacentDilationCoeff m ((q : ℕ) ^ m) = 1 := by
  classical
  have hq0 : ((q : ℕ) ^ m) ≠ 0 := pow_ne_zero _ q.2.ne_zero
  rw [adjacentDilationCoeff_apply hq0, if_pos ⟨(q : ℕ), rfl⟩, if_neg, sub_zero]
  rintro ⟨b, hb⟩
  have hΩ : Ω ((q : ℕ) ^ m) = m := by
    rw [cardFactors_pow, cardFactors_apply_prime q.2, mul_one]
  rw [hb, cardFactors_pow] at hΩ
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : m + 1 ≠ 0)] at hb
    exact hq0 hb
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, one_pow] at hb
    have h2 : (2 : ℕ) ≤ (q : ℕ) ^ m := by
      calc (2 : ℕ) ≤ (q : ℕ) := q.2.two_le
        _ = (q : ℕ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (q : ℕ) ^ m := Nat.pow_le_pow_right q.2.one_lt.le hm
    rw [hb] at h2
    omega
  have hΩb : 1 ≤ Ω b := by
    rcases Nat.eq_zero_or_pos (Ω b) with h0 | hpos
    · rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h' | h'
      · exact absurd h' hb0
      · exact absurd h' hb1
    · exact hpos
  have hmul : m + 1 ≤ (m + 1) * Ω b := Nat.le_mul_of_pos_right _ hΩb
  omega

end

end RHTower.AdjacentDilation

namespace RHTower.AdjacentDilation

open ArithmeticFunction
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open RHTower

noncomputable section

/-- The selected prime derivative of an adjacent-dilation jet has no coefficient below grade
`m-1`. -/
theorem primeDeriv_rotatedAdjacentJet_eq_zero_of_cardFactors_lt
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n < m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (adjacentDilationCoeff m)) n = 0 := by
  rw [primeDeriv_apply]
  by_cases hn : n = 0
  · subst n
    simp
  have hnq0 : n * q.1 ≠ 0 := mul_ne_zero hn q.2.ne_zero
  by_cases hcoeff : adjacentDilationCoeff m (n * q.1) = 0
  · simp [rotatedLogArithmeticJet_apply, hcoeff]
  have hlower := adjacentDilationCoeff_cardFactors_lower hm hcoeff
  have hmul := cardFactors_mul hn q.2.ne_zero
  rw [cardFactors_apply_prime q.2] at hmul
  rw [hmul] at hlower
  exact False.elim (by omega)

/-- On its lowest grade, the selected prime derivative of an adjacent-dilation jet is one point
mass. -/
theorem primeDeriv_rotatedAdjacentJet_eq_pointMass_of_cardFactors_eq
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n = m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (adjacentDilationCoeff m)) n =
      arithmeticPointMass (q.1 ^ (m - 1))
        ((m : ℂ) * (((m : ℂ) * rotatedPrimeLogClock q) ^ k)) n := by
  by_cases htarget : n = q.1 ^ (m - 1)
  · subst n
    rw [primeDeriv_apply]
    have hpow : q.1 ^ (m - 1) * q.1 = q.1 ^ m := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow, rotatedLogArithmeticJet_apply, adjacentDilationCoeff_prime_pow hm q,
      Nat.Prime.factorization_pow q.2,
      arithmeticPointMass_apply_self (pow_ne_zero _ q.2.ne_zero)]
    simp only [Finsupp.single_eq_same, mul_one]
    have hlog : (Real.log ((q.1 ^ m : ℕ) : ℝ) : ℂ) =
        (m : ℂ) * (Real.log q.1 : ℂ) := by
      rw [show ((q.1 ^ m : ℕ) : ℝ) = (q.1 : ℝ) ^ m by norm_num, Real.log_pow]
      exact_mod_cast rfl
    rw [hlog]
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  · rw [arithmeticPointMass_apply_of_ne (pow_ne_zero _ q.2.ne_zero) htarget]
    rw [primeDeriv_apply]
    by_cases hn : n = 0
    · subst n
      simp
    by_cases hcoeff : adjacentDilationCoeff m (n * q.1) = 0
    · simp [rotatedLogArithmeticJet_apply, hcoeff]
    exfalso
    have hmulΩ := cardFactors_mul hn q.2.ne_zero
    rw [cardFactors_apply_prime q.2, hΩ] at hmulΩ
    have hΩcoeff : Ω (n * q.1) = m := by omega
    obtain ⟨p, hpure⟩ :=
      adjacentDilationCoeff_eq_prime_pow_of_cardFactors_eq hm hcoeff hΩcoeff
    have hqdvd : q.1 ∣ p.1 ^ m := by
      rw [← hpure]
      exact ⟨n, by ring⟩
    have hpq : q = p := by
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqdvd
    subst p
    apply htarget
    apply Nat.eq_of_mul_eq_mul_right q.2.pos
    calc
      n * q.1 = q.1 ^ m := hpure
      _ = q.1 ^ (m - 1) * q.1 := by
        rw [← pow_succ]
        congr 1
        omega

end

end RHTower.AdjacentDilation

namespace RHTower.AdjacentDilation

open ArithmeticFunction
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open RHTower

noncomputable section

/-- The unified family: zeta at level one and the adjacent-dilation coefficients above. -/
def zetaAdjacentArithmetic (m : ℕ) : ArithmeticFunction ℂ :=
  if m = 1 then zetaArith else adjacentDilationCoeff m

@[simp]
theorem zetaAdjacentArithmetic_one :
    zetaAdjacentArithmetic 1 = zetaArith := by
  simp [zetaAdjacentArithmetic]

theorem zetaAdjacentArithmetic_eq_adjacent {m : ℕ} (hm : m ≠ 1) :
    zetaAdjacentArithmetic m = adjacentDilationCoeff m := by
  simp [zetaAdjacentArithmetic, hm]

theorem primeDeriv_rotatedZetaAdjacentJet_eq_zero_of_cardFactors_lt
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n < m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (zetaAdjacentArithmetic m)) n = 0 := by
  by_cases hm1 : m = 1
  · omega
  · rw [zetaAdjacentArithmetic_eq_adjacent hm1]
    exact primeDeriv_rotatedAdjacentJet_eq_zero_of_cardFactors_lt hm q k n hΩ

theorem primeDeriv_rotatedZetaAdjacentJet_eq_pointMass_of_cardFactors_eq
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n = m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (zetaAdjacentArithmetic m)) n =
      arithmeticPointMass (q.1 ^ (m - 1))
        ((m : ℂ) * (((m : ℂ) * rotatedPrimeLogClock q) ^ k)) n := by
  by_cases hm1 : m = 1
  · subst m
    simp only [zetaAdjacentArithmetic_one, Nat.reduceSubDiff, pow_zero,
      Nat.cast_one, one_mul]
    exact primeDeriv_rotatedZetaJet_eq_pointMass_of_cardFactors_eq_zero q k n
      (by simpa using hΩ)
  · rw [zetaAdjacentArithmetic_eq_adjacent hm1]
    exact primeDeriv_rotatedAdjacentJet_eq_pointMass_of_cardFactors_eq hm q k n hΩ

/-- **Theorem 1, jet form.**  Every finite rectangle of jets of the unified zeta/adjacent-dilation
family at distinct positive levels is algebraically independent. -/
theorem zetaAdjacentJets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) (jet : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (jet + 1) =>
        rotatedLogArithmeticJet x.2 (zetaAdjacentArithmetic (level x.1))) := by
  apply omegaLeadingJets_algebraicIndependent
    (fun r => zetaAdjacentArithmetic (level r)) level hpos hinj
  · intro r q k n hn
    exact primeDeriv_rotatedZetaAdjacentJet_eq_zero_of_cardFactors_lt (hpos r) q k n hn
  · intro r q k n hn
    exact primeDeriv_rotatedZetaAdjacentJet_eq_pointMass_of_cardFactors_eq (hpos r) q k n hn

/-- **Theorem 1.**  Zeta together with any distinct positive adjacent-dilation levels is
differentially independent in the Dirichlet-convolution fraction field. -/
theorem zetaAdjacentArithmetic_differentialIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (zetaAdjacentArithmetic (level r))) := by
  unfold DifferentialIndependent
  simp_rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
  let x : Fin d → ℕ → arithmeticFunctionFractionField := fun r k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet k (zetaAdjacentArithmetic (level r)))
  apply algebraicIndependent_prod_nat_of_fin x
  intro jet
  have hraw := zetaAdjacentJets_algebraicIndependent level hpos hinj jet
  have hmap := hraw.map'
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (IsFractionRing.injective (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
  simpa only [Function.comp_apply, x] using! hmap

end

end RHTower.AdjacentDilation

namespace RHTower.AdjacentDilation

open ArithmeticFunction
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open RHTower

noncomputable section

/-- The adjacent-dilation coefficient stream is bounded, hence of finite abscissa. -/
def adjacentDilationFiniteAbscissaSource (m : ℕ) :
    finiteAbscissaArithmeticSubalgebra := by
  classical
  refine ⟨adjacentDilationCoeff m, 1, ?_⟩
  intro y hy
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    by_cases h0 : n = 0
    · simp [adjacentDilationCoeff, h0]
    rw [adjacentDilationCoeff_apply h0]
    by_cases ha : ∃ a : ℕ, n = a ^ m <;> by_cases hb : ∃ b : ℕ, n = b ^ (m + 1) <;>
      simp [ha, hb]
  · simpa using hy

@[simp]
theorem adjacentDilationFiniteAbscissaSource_val (m : ℕ) :
    (adjacentDilationFiniteAbscissaSource m).1 = adjacentDilationCoeff m :=
  rfl

/-- Finite-abscissa source for the unified zeta/adjacent family. -/
def zetaAdjacentFiniteAbscissaSource (m : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  if m = 1 then zetaSource else adjacentDilationFiniteAbscissaSource m

@[simp]
theorem zetaAdjacentFiniteAbscissaSource_val (m : ℕ) :
    (zetaAdjacentFiniteAbscissaSource m).1 = zetaAdjacentArithmetic m := by
  by_cases hm : m = 1
  · subst m
    simp [zetaAdjacentFiniteAbscissaSource]
  · simp [zetaAdjacentFiniteAbscissaSource, zetaAdjacentArithmetic, hm]

/-- Actual upper-end meromorphic carrier of the adjacent-dilation Dirichlet series. -/
def adjacentDilationUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero (adjacentDilationFiniteAbscissaSource m)

/-- Actual upper-end meromorphic carrier of the unified zeta/adjacent source. -/
def zetaAdjacentUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero (zetaAdjacentFiniteAbscissaSource m)

@[simp]
theorem zetaAdjacentUpperEndCarrier_one :
    zetaAdjacentUpperEndCarrier 1 = zetaUpperEndMero := rfl

theorem zetaAdjacentUpperEndCarrier_eq_adjacent {m : ℕ} (hm : m ≠ 1) :
    zetaAdjacentUpperEndCarrier m = adjacentDilationUpperEndCarrier m := by
  simp [zetaAdjacentUpperEndCarrier, zetaAdjacentFiniteAbscissaSource, hm,
    adjacentDilationUpperEndCarrier]

theorem zetaAdjacentArithmetic_differentialIndependent_fintype
    {I : Type*} [Fintype I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (zetaAdjacentArithmetic (level i))) := by
  classical
  let E : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hfin :=
    zetaAdjacentArithmetic_differentialIndependent
      (fun r => level (E.symm r))
      (fun r => hpos (E.symm r))
      (hinj.comp E.symm.injective)
  have hcomp := hfin.comp E E.injective
  convert hcomp using 1
  funext i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- **Theorem 1, analytic form.**  Zeta together with every finite packet of distinct positive
adjacent-dilation levels is jointly differentially independent over the actual rational-coordinate
field. -/
theorem zetaAdjacentUpperEndCarrier_differentialIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => zetaAdjacentUpperEndCarrier (level i)) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  simpa [zetaAdjacentUpperEndCarrier] using
    zetaAdjacentArithmetic_differentialIndependent_fintype level hpos hinj

/-- Arbitrarily many distinct positive members of the unified family remain jointly differentially
independent over the rational coordinate. -/
theorem zetaAdjacentUpperEndCarrier_differentialIndependent_of_injective
    {I : Type*} (level : I → ℕ)
    (hpos : ∀ i, 0 < level i) (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => zetaAdjacentUpperEndCarrier (level i)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro J hJfinite
  by_cases hJempty : J = ∅
  · subst J
    exact algebraicIndependent_empty_type
  letI : Fintype J := hJfinite.fintype
  letI : Nonempty J :=
    Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hJempty)
  apply zetaAdjacentUpperEndCarrier_differentialIndependent (fun j : J => level j)
  · intro j
    exact hpos j
  · intro i j hij
    exact Subtype.ext (hinj hij)

/-- **Theorem 1 for the card's family.**  Zeta itself and every adjacent direct-dilation
difference from level two onward form one countably infinite jointly differentially independent
family over the rational coordinate field. -/
theorem zetaAdjacentDilationUpperEnd_differentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun m : {m : ℕ // 2 ≤ m} => adjacentDilationUpperEndCarrier m.1)) := by
  classical
  let level : Unit ⊕ {m : ℕ // 2 ≤ m} → ℕ := Sum.elim (fun _ => 1) (fun m => m.1)
  have hpos : ∀ i, 0 < level i := by
    rintro (u | m)
    · exact Nat.one_pos
    · have hm := m.2
      show 0 < (m : ℕ)
      omega
  have hinj : Function.Injective level := by
    rintro (u | m) (v | n) h
    · cases u; cases v; rfl
    · exfalso
      have h' : (1 : ℕ) = (n : ℕ) := h
      have hn := n.2
      omega
    · exfalso
      have h' : (m : ℕ) = 1 := h
      have hm := m.2
      omega
    · have h' : (m : ℕ) = (n : ℕ) := h
      exact congrArg Sum.inr (Subtype.ext h')
  have hfun : (Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun m : {m : ℕ // 2 ≤ m} => adjacentDilationUpperEndCarrier m.1))
      = fun i => zetaAdjacentUpperEndCarrier (level i) := by
    funext i
    rcases i with u | m
    · rfl
    · have hm := m.2
      exact (zetaAdjacentUpperEndCarrier_eq_adjacent (by omega : (m : ℕ) ≠ 1)).symm
  rw [hfun]
  exact zetaAdjacentUpperEndCarrier_differentialIndependent_of_injective level hpos hinj

end

end RHTower.AdjacentDilation
