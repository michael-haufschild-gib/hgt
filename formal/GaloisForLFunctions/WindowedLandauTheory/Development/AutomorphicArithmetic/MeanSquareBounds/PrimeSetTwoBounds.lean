import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.PairGood
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionCounts

/-! Prime sets and quadratic twist estimates used in the two stages of host selection. -/

open Finset ArithmeticFunction

noncomputable section

namespace QH

open UpperTheory.Top WindowedLandauTheory.HC

/-- The truncated coefficient for the smoothed sum after subtracting its linear term. -/
def cN (y : ℝ) (n : ℕ) : ℝ :=
  vonMangoldt n * min 1 (y / n)

def S (Z y : ℝ) (q : ℕ) (κ : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊Z⌋₊, (cN y n : ℂ) * κ n * J q n

structure AdmissiblePrimeScale (ε Y U : ℝ) (m₀ a₀ : ℕ) : Prop where
  pos : 0 < m₀
  eight : 8 ∣ m₀
  coprime : a₀.Coprime m₀
  log_m : (1 / 4) * Real.log Y ^ 2 * Real.log m₀ ≤ Real.log U
  lo : Y ^ (ε / 6) ≤ Real.log U
  hi : Real.log U ≤ Y ^ (ε / 5) * Real.log Y ^ 2

def MeanSq (C Z : ℝ) (P : Finset ℕ) (A : Set ℝ) : Prop :=
  ∀ y ∈ A, ∀ κ : ℕ → ℂ, (∀ n, ‖κ n‖ ≤ 1) →
    ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ C * y * Real.log y * P.card

def GoodC (Q : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  ψ ≠ 1 ∧ (N : ℝ) ≤ Q ∧ ZeroBox Q ψ

def Box (Q C τ Y X : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  GoodC Q ψ ∧ ‖An.logDerivativeAtOne ψ‖ ≤ C * Real.log Y ∧
    ∀ y ∈ Set.Icc Y X, ‖An.gChi ψ y‖ ≤ y ^ (1 / 2 + τ)

def BoxAll (Q C τ Y X : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N), An.Induces ψ f M → Box Q C τ Y X ψ

/-- Primes in the indicated residue class in the interval `(√X, X]`. -/
def PPset (m a : ℕ) (X : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % m = a % m ∧ X ^ (1 / 2 : ℝ) < (p : ℝ))

def oddM (z : ℝ) (q : ℕ) : ℕ :=
  q * ∏ p ∈ (Icc 3 ⌊z⌋₊).filter Nat.Prime, p

def primePairSetFirst (z : ℝ) : Finset ℕ :=
  PPset 8 3 (Real.exp z)

def primeSetTwoBounds (z z' : ℝ) (q : ℕ) : Finset ℕ :=
  (Icc 1 ⌊Real.exp z'⌋₊).filter fun d =>
    d.Prime ∧ d % 16 = 7 ∧ oddM z q ∣ d + 1 ∧ Real.exp z' ^ (1 / 2 : ℝ) < (d : ℝ)

def GoodQ (N₀ : ℕ) (C τ Y X z : ℝ) (q : ℕ) : Prop :=
  ∀ ξ : DirichletCharacter ℂ N₀, BoxAll (N₀ * Real.exp z) C τ Y X (fun n => ξ n * J q n) (N₀ * q)

def GoodD (N₀ : ℕ) (C τ Y X z z' : ℝ) (q d : ℕ) : Prop :=
  ∀ ξ : DirichletCharacter ℂ N₀, ∀ a : ℕ, a ≤ 1 →
    BoxAll (N₀ * Real.exp (z + z')) C τ Y X (fun n => ξ n * J q n ^ a * J d n) (N₀ * q * d)

structure Rows (z z' : ℝ) (q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_gt : z / 2 < Real.log q
  q_le : Real.log q ≤ z
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_gt : z' / 2 < Real.log d
  d_le : Real.log d ≤ z'
  q_lt_d : q < d
  d_class : ∀ p : ℕ, p.Prime → p ≠ 2 → ((p : ℝ) ≤ z ∨ p = q) → (d + 1) % p = 0

theorem rows_of_mem {z z' : ℝ} {q d : ℕ} (hzz : 2 * z ≤ z')
    (hq : q ∈ primePairSetFirst z) (hd : d ∈ primeSetTwoBounds z z' q) :
    Rows z z' q d := by
  have hhalf (t : ℝ) : Real.exp t ^ (1 / 2 : ℝ) = Real.exp (t / 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  simp only [primePairSetFirst, PPset, primeSetTwoBounds, mem_filter, mem_Icc, hhalf] at hq hd
  obtain ⟨⟨_, hq₂⟩, hqp, hqm, hqg⟩ := hq
  obtain ⟨⟨_, hd₂⟩, hdp, hdm, hdv, hdg⟩ := hd
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast hdp.pos
  have hqle := (Nat.le_floor_iff (Real.exp_pos z).le).mp hq₂
  have hdle := (Nat.le_floor_iff (Real.exp_pos z').le).mp hd₂
  refine ⟨hqp, by simpa using hqm, (Real.lt_log_iff_exp_lt hq₀).mpr hqg,
    (Real.log_le_iff_le_exp hq₀).mpr hqle, hdp, hdm, (Real.lt_log_iff_exp_lt hd₀).mpr hdg,
    (Real.log_le_iff_le_exp hd₀).mpr hdle, ?_, ?_⟩
  · have h : (q : ℝ) < d :=
      lt_of_le_of_lt (hqle.trans (Real.exp_le_exp.mpr (by linarith only [hzz]))) hdg
    exact_mod_cast h
  · intro p hp hp₂ hpz
    apply Nat.mod_eq_zero_of_dvd
    refine dvd_trans ?_ hdv
    rcases hpz with hpz | rfl
    · unfold oddM
      apply Dvd.dvd.mul_left
      exact Finset.dvd_prod_of_mem id
        (mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := hp.two_le; omega, Nat.le_floor hpz⟩, hp⟩)
    · exact dvd_mul_right _ _

private theorem two_coprime_oddM (z : ℝ) {q : ℕ} (hq : q.Prime) (h₂ : q ≠ 2) :
    Nat.Coprime 2 (oddM z q) := by
  refine Nat.Coprime.mul_right ((Nat.coprime_primes Nat.prime_two hq).mpr h₂.symm)
    (Nat.Coprime.prod_right fun p hp => ?_)
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  have h₃ := (mem_Icc.mp hpI).1
  exact (Nat.coprime_primes Nat.prime_two hpp).mpr (by omega)

/-- The second prime set lies in one reduced residue class, obtained by the Chinese remainder theorem. -/
theorem exists_coprime_primePairSetSecond_eq_PPset (z z' : ℝ) {q : ℕ} (hq : q.Prime) (h₂ : q ≠ 2) :
    ∃ a₀ : ℕ, a₀.Coprime (16 * oddM z q) ∧
      primeSetTwoBounds z z' q = PPset (16 * oddM z q) a₀ (Real.exp z') := by
  let m := oddM z q
  have hcop := two_coprime_oddM z hq h₂
  have hm : 0 < m := by
    exact Nat.mul_pos hq.pos (prod_pos fun p hp => (mem_filter.mp hp).2.pos)
  have h16 : Nat.Coprime 16 m := by simpa using hcop.pow_left 4
  obtain ⟨a, ha⟩ := GaloisForLFunctions.BezoutValuationIncidence.exists_coprime_residue_intersection
    (a := 7) (b := m - 1) h16
  have hac := (ha a).mpr (Nat.ModEq.refl a)
  have hdvd (d : ℕ) : m ∣ d + 1 ↔ d ≡ m - 1 [MOD m] := by
    rw [← Nat.modEq_zero_iff_dvd]
    have hzero : m - 1 + 1 ≡ 0 [MOD m] := by
      rw [Nat.sub_add_cancel hm]
      exact Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    constructor
    · intro hd
      exact Nat.ModEq.add_right_cancel' 1 (hd.trans hzero.symm)
    · intro hd
      exact (hd.add_right 1).trans hzero
  have ham : a.Coprime m := Nat.Coprime.coprime_dvd_right ((hdvd a).mpr hac.2)
    (by rw [Nat.coprime_self_add_right]; exact Nat.coprime_one_right a)
  have ha16 : a.Coprime 16 := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hac.1]
    norm_num
  refine ⟨a, Nat.Coprime.mul_right ha16 ham, ?_⟩
  unfold primeSetTwoBounds PPset
  apply Finset.filter_congr
  intro d _
  change (d.Prime ∧ d % 16 = 7 ∧ m ∣ d + 1 ∧ _) ↔ (d.Prime ∧ d ≡ a [MOD 16 * m] ∧ _)
  rw [← ha d, ← hdvd d]
  change (d.Prime ∧ d % 16 = 7 ∧ m ∣ d + 1 ∧ _) ↔
    (d.Prime ∧ (d % 16 = 7 ∧ m ∣ d + 1) ∧ _)
  tauto

theorem log_oddM {z : ℝ} {q : ℕ} (hz : 0 ≤ z) (hq : 0 < q) :
    Real.log ((16 * oddM z q : ℕ) : ℝ) ≤ Real.log 16 + Real.log q + z * Real.log 4 := by
  let P := ∏ p ∈ (Icc 3 ⌊z⌋₊).filter Nat.Prime, p
  have hP : P ≤ 4 ^ ⌊z⌋₊ := by
    refine le_trans ?_ (primorial_le_four_pow ⌊z⌋₊)
    unfold P primorial
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro p hp
      simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      exact (mem_filter.mp hp).2.one_lt.le
  have hP₀ : 0 < P := prod_pos fun p hp => (mem_filter.mp hp).2.pos
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP₀
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hPr' : (P : ℝ) ≤ (4 : ℝ) ^ ⌊z⌋₊ := by exact_mod_cast hP
  change Real.log ((16 * (q * P) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity),
    Real.log_mul hqR.ne' hPr.ne']
  have hlog := Real.log_le_log hPr hPr'
  rw [Real.log_pow] at hlog
  have hh := mul_le_mul_of_nonneg_right (Nat.floor_le hz)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
  linarith only [hlog, hh]

end QH

end
