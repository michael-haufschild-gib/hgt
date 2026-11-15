import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierIterates
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierParameterExpansion

/-!
# Iterated Cartier extraction on monomial differentials

The `e`th iterate selects exponents congruent to `p^e-1` modulo `p^e`.
The formula holds for every function, including nonseparating parameters,
and gives coefficient extraction from arbitrary `p^e`-power expansions.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c b R
local notation "D" => KaehlerDifferential.D K L
local notation "C" => squareKummerCoordinateCartier p s c b R
local notation "I" => squareKummerCartierIterate p s c b R

private theorem characteristicPower_pred (e : ℕ) :
    p ^ (e + 1) - 1 = (p ^ e - 1) * p + (p - 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have he : 1 ≤ p ^ e := Nat.one_le_pow e p hp
  have hmul : (p ^ e - 1) * p + p = p ^ e * p := by
    calc
      (p ^ e - 1) * p + p = (p ^ e - 1) * p + 1 * p := by rw [one_mul]
      _ = (p ^ e - 1 + 1) * p := (Nat.add_mul _ _ _).symm
      _ = p ^ e * p := by rw [Nat.sub_add_cancel he]
  have hpow : 1 ≤ p ^ (e + 1) := Nat.one_le_pow _ _ hp
  have hsucc := Nat.sub_add_cancel hpow
  rw [pow_succ] at hsucc
  rw [pow_succ]
  omega

/-- Cartier selects exactly the monomial exponents congruent to `p-1` modulo `p`. -/
theorem squareKummerCoordinateCartier_monomial (t : L) (j : ℕ) :
    C (t ^ j • D t) =
      if j % p = p - 1 then t ^ (j / p) • D t else 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hfactor : t ^ j • D t =
      (t ^ (j / p)) ^ p • (t ^ (j % p) • D t) := by
    rw [smul_smul, ← pow_mul, ← pow_add, Nat.mul_comm (j / p) p, Nat.div_add_mod]
  rw [hfactor, squareKummerCoordinateCartier_frobenius_smul,
    squareKummerCoordinateCartier_parameter_monomial p s c b R t ⟨j % p, Nat.mod_lt j hp⟩]
  by_cases h : j % p = p - 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, smul_zero]

/-- The top monomial in a `p^e`-term parameter expansion survives the `e`th Cartier iterate. -/
theorem squareKummerCartierIterate_normalization (e : ℕ) (t : L) :
    I e (t ^ (p ^ e - 1) • D t) = D t := by
  induction e with
  | zero => simp only [pow_zero, Nat.sub_self, one_smul, squareKummerCartierIterate_zero]
  | succ e ih =>
    have hfactor : t ^ (p ^ (e + 1) - 1) • D t =
        (t ^ (p ^ e - 1)) ^ p • (t ^ (p - 1) • D t) := by
      rw [smul_smul, ← pow_mul, ← pow_add, characteristicPower_pred]
    rw [squareKummerCartierIterate_add]
    change I e (C (t ^ (p ^ (e + 1) - 1) • D t)) = D t
    rw [hfactor, squareKummerCoordinateCartier_frobenius_smul,
      squareKummerCoordinateCartier_normalization, ih]

/-- Every lower monomial in a `p^e`-term parameter expansion is killed by the `e`th iterate. -/
theorem squareKummerCartierIterate_lower_monomial (e : ℕ) (t : L)
    (j : ℕ) (hj : j < p ^ e - 1) : I e (t ^ j • D t) = 0 := by
  induction e generalizing j with
  | zero => simp only [pow_zero, Nat.sub_self] at hj; omega
  | succ e ih =>
    rw [squareKummerCartierIterate_add]
    change I e (C (t ^ j • D t)) = 0
    rw [squareKummerCoordinateCartier_monomial]
    by_cases hmod : j % p = p - 1
    · rw [if_pos hmod]
      apply ih
      by_contra h
      have hle : p ^ e - 1 ≤ j / p := Nat.le_of_not_gt h
      have hmul := Nat.mul_le_mul_right p hle
      have hdiv := Nat.div_add_mod j p
      rw [hmod, Nat.mul_comm p (j / p)] at hdiv
      rw [characteristicPower_pred] at hj
      omega
    · rw [if_neg hmod, map_zero]

/-- An arbitrary monomial survives precisely in the top residue class modulo `p^e`. -/
theorem squareKummerCartierIterate_monomial (e : ℕ) (t : L) (j : ℕ) :
    I e (t ^ j • D t) =
      if j % (p ^ e) = p ^ e - 1 then t ^ (j / (p ^ e)) • D t else 0 := by
  have hpe : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hfactor : t ^ j • D t =
      (t ^ (j / (p ^ e))) ^ (p ^ e) • (t ^ (j % (p ^ e)) • D t) := by
    rw [smul_smul, ← pow_mul, ← pow_add, Nat.mul_comm (j / (p ^ e)) (p ^ e),
      Nat.div_add_mod]
  rw [hfactor, squareKummerCartierIterate_frobenius_smul]
  by_cases h : j % (p ^ e) = p ^ e - 1
  · rw [if_pos h, h, squareKummerCartierIterate_normalization]
  · have hlt : j % (p ^ e) < p ^ e - 1 := by
      have hm := Nat.mod_lt j hpe
      omega
    rw [if_neg h, squareKummerCartierIterate_lower_monomial p s c b R e t _ hlt, smul_zero]

/-- Iterated Cartier extracts the top coefficient from every actual `p^e`-power parameter expansion. -/
theorem squareKummerCartierIterate_parameter_expansion (e : ℕ) (t : L)
    (a : Fin (p ^ e) → L) (j : Fin (p ^ e)) (hj : j.val = p ^ e - 1) :
    I e (∑ i : Fin (p ^ e), a i ^ (p ^ e) • (t ^ i.val • D t)) = a j • D t := by
  classical
  rw [map_sum]
  calc
    _ = ∑ i : Fin (p ^ e), if i = j then a j • D t else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [squareKummerCartierIterate_frobenius_smul]
      by_cases hi : i = j
      · subst i
        rw [if_pos rfl, hj, squareKummerCartierIterate_normalization]
      · have hival : i.val ≠ p ^ e - 1 := fun h => hi (Fin.ext (h.trans hj.symm))
        have hlt : i.val < p ^ e - 1 := by have h := i.isLt; omega
        rw [if_neg hi, squareKummerCartierIterate_lower_monomial p s c b R e t _ hlt, smul_zero]
    _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

