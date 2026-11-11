import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergCorrectionKeepsItsSummableEnvelope
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCoefficientIdentity

/-!
# Multiplicativity and prime-power fibres of the shifted correction

Pair-coprime supports split the correction convolution into independent
prime factors. At two positive powers of a prime only the squarefree
support consisting of that prime contributes.
-/

open ArithmeticFunction Finset
open RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

@[simp] theorem powerShiftedReciprocalAmplitude_one (s : ℝ) :
    powerShiftedReciprocalAmplitude s 1 = 1 :=
  (isMultiplicative_powerShiftedReciprocalAmplitude s).map_one

@[simp] theorem localizedShiftedSelbergAmplitude_one (s : ℝ) (r : ℕ) :
    localizedShiftedSelbergAmplitude s r 1 = 1 := by
  simp [localizedShiftedSelbergAmplitude]

theorem localizedShiftedSelbergAmplitude_mul_of_coprime (s : ℝ)
    {r₁ r₂ u₁ u₂ : ℕ} (h : Nat.Coprime (r₁ * u₁) (r₂ * u₂)) :
    localizedShiftedSelbergAmplitude s (r₁ * r₂) (u₁ * u₂) =
      localizedShiftedSelbergAmplitude s r₁ u₁ *
        localizedShiftedSelbergAmplitude s r₂ u₂ := by
  classical
  have hu : Nat.Coprime u₁ u₂ :=
    h.of_dvd_left (dvd_mul_of_dvd_right (dvd_refl u₁) r₁)
      |>.of_dvd_right (dvd_mul_of_dvd_right (dvd_refl u₂) r₂)
  have hamp := (isMultiplicative_powerShiftedReciprocalAmplitude s).map_mul_of_coprime hu
  rw [show localizedShiftedSelbergAmplitude s (r₁ * r₂) (u₁ * u₂) =
      if primeSupportedOn (r₁ * r₂) (u₁ * u₂) then
        powerShiftedReciprocalAmplitude s (u₁ * u₂) else 0 by
      rfl,
    show localizedShiftedSelbergAmplitude s r₁ u₁ =
      if primeSupportedOn r₁ u₁ then powerShiftedReciprocalAmplitude s u₁ else 0 by
      rfl,
    show localizedShiftedSelbergAmplitude s r₂ u₂ =
      if primeSupportedOn r₂ u₂ then powerShiftedReciprocalAmplitude s u₂ else 0 by
      rfl,
    primeSupportedOn_mul_iff_of_coprime h, hamp]
  by_cases h₁ : primeSupportedOn r₁ u₁ <;>
    by_cases h₂ : primeSupportedOn r₂ u₂ <;> simp [h₁, h₂]

theorem shiftedSelbergCorrectionWeight_mul_of_coprime (s : ℝ)
    {r₁ r₂ u₁ u₂ v₁ v₂ : ℕ}
    (h : Nat.Coprime (r₁ * u₁ * v₁) (r₂ * u₂ * v₂)) :
    shiftedSelbergCorrectionWeight s (r₁ * r₂) (u₁ * u₂) (v₁ * v₂) =
      shiftedSelbergCorrectionWeight s r₁ u₁ v₁ * shiftedSelbergCorrectionWeight s r₂ u₂ v₂ := by
  have hr : Nat.Coprime r₁ r₂ :=
    h.of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right r₁ u₁) v₁)
      |>.of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right r₂ u₂) v₂)
  have hu : Nat.Coprime (r₁ * u₁) (r₂ * u₂) :=
    h.of_dvd_left (dvd_mul_right (r₁ * u₁) v₁)
      |>.of_dvd_right (dvd_mul_right (r₂ * u₂) v₂)
  have hv : Nat.Coprime (r₁ * v₁) (r₂ * v₂) := by
    apply h.of_dvd_left
      (show r₁ * v₁ ∣ r₁ * u₁ * v₁ by
        refine ⟨u₁, by ring⟩)
      |>.of_dvd_right
        (show r₂ * v₂ ∣ r₂ * u₂ * v₂ by
          refine ⟨u₂, by ring⟩)
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hr
  rw [shiftedSelbergCorrectionWeight, shiftedSelbergCorrectionWeight, shiftedSelbergCorrectionWeight,
    localizedShiftedSelbergAmplitude_mul_of_coprime s hu,
    localizedShiftedSelbergAmplitude_mul_of_coprime s hv, hmu]
  push_cast
  ring

private theorem quotient_mul_quotient_eq' {a c x y : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hx : x ∣ a) (hy : y ∣ c) :
    (a * c) / (x * y) = (a / x) * (c / y) := by
  have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hx ha
  have hypos : 0 < y := Nat.pos_of_dvd_of_pos hy hc
  apply Nat.div_eq_of_eq_mul_left (mul_pos hxpos hypos)
  calc
    a * c = ((a / x) * x) * ((c / y) * y) := by
      rw [Nat.div_mul_cancel hx, Nat.div_mul_cancel hy]
    _ = ((a / x) * (c / y)) * (x * y) := by ring

/-- Bivariate coefficient obtained by pushing the three-variable Euler correction along
`(r,u,v) ↦ (r*u,r*v)`. -/
def shiftedSelbergCorrectionCoeff (s : ℝ) (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else
    ∑ r : {r // r ∈ (Nat.gcd m n).divisors},
      shiftedSelbergCorrectionWeight s r.1 (m / r.1) (n / r.1)

@[simp] theorem shiftedSelbergCorrectionCoeff_one (s : ℝ) :
    shiftedSelbergCorrectionCoeff s 1 1 = 1 := by
  let z₀ : {r // r ∈ (Nat.gcd 1 1).divisors} := ⟨1, by simp⟩
  rw [shiftedSelbergCorrectionCoeff, if_neg (by simp), Fintype.sum_eq_single z₀]
  · simp [z₀, shiftedSelbergCorrectionWeight, localizedShiftedSelbergAmplitude, powerShiftedReciprocalAmplitude_one]
  · intro z hz
    exfalso
    apply hz
    apply Subtype.ext
    exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2)

/-- The pushed Euler correction is bivariate multiplicative. -/
theorem bivariateMultiplicative_shiftedSelbergCorrectionCoeff (s : ℝ) :
    BivariateMultiplicative (shiftedSelbergCorrectionCoeff s) := by
  constructor
  · exact shiftedSelbergCorrectionCoeff_one s
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · rcases Nat.mul_eq_zero.mp hab0 with rfl | rfl <;>
        simp [shiftedSelbergCorrectionCoeff]
    by_cases hcd0 : c * d = 0
    · rcases Nat.mul_eq_zero.mp hcd0 with rfl | rfl <;>
        simp [shiftedSelbergCorrectionCoeff]
    have ha : 0 < a := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hc : 0 < c := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hd : 0 < d := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    let g₁ := Nat.gcd a b
    let g₂ := Nat.gcd c d
    have hg₁ : 0 < g₁ := Nat.gcd_pos_of_pos_left b ha
    have hg₂ : 0 < g₂ := Nat.gcd_pos_of_pos_left d hc
    have hg : Nat.Coprime g₁ g₂ :=
      h.of_dvd_left (dvd_trans (Nat.gcd_dvd_left a b) (dvd_mul_right a b))
        |>.of_dvd_right
          (dvd_trans (Nat.gcd_dvd_left c d) (dvd_mul_right c d))
    let e := coprimeDivisorsEquiv hg₁.ne' hg₂.ne' hg
    simp only [shiftedSelbergCorrectionCoeff,
      if_neg (not_or_intro (Nat.mul_ne_zero ha.ne' hc.ne')
        (Nat.mul_ne_zero hb.ne' hd.ne')),
      if_neg (not_or_intro ha.ne' hb.ne'),
      if_neg (not_or_intro hc.ne' hd.ne')]
    rw [gcd_pair_mul_of_pair_coprime h]
    change (∑ r : {r // r ∈ (g₁ * g₂).divisors},
        shiftedSelbergCorrectionWeight s r.1 ((a * c) / r.1) ((b * d) / r.1)) = _
    calc
      (∑ r : {r // r ∈ (g₁ * g₂).divisors},
          shiftedSelbergCorrectionWeight s r.1 ((a * c) / r.1) ((b * d) / r.1)) =
          ∑ q : ({r // r ∈ g₁.divisors} × {r // r ∈ g₂.divisors}),
            shiftedSelbergCorrectionWeight s (e q).1
              ((a * c) / (e q).1) ((b * d) / (e q).1) := by
        exact (e.sum_comp (fun r => shiftedSelbergCorrectionWeight s r.1
          ((a * c) / r.1) ((b * d) / r.1))).symm
      _ = ∑ q : ({r // r ∈ g₁.divisors} × {r // r ∈ g₂.divisors}),
          shiftedSelbergCorrectionWeight s q.1.1 (a / q.1.1) (b / q.1.1) *
            shiftedSelbergCorrectionWeight s q.2.1 (c / q.2.1) (d / q.2.1) := by
        apply Fintype.sum_congr
        intro q
        have hr₁a : q.1.1 ∣ a := dvd_trans
          (Nat.dvd_of_mem_divisors q.1.2) (Nat.gcd_dvd_left a b)
        have hr₁b : q.1.1 ∣ b := dvd_trans
          (Nat.dvd_of_mem_divisors q.1.2) (Nat.gcd_dvd_right a b)
        have hr₂c : q.2.1 ∣ c := dvd_trans
          (Nat.dvd_of_mem_divisors q.2.2) (Nat.gcd_dvd_left c d)
        have hr₂d : q.2.1 ∣ d := dvd_trans
          (Nat.dvd_of_mem_divisors q.2.2) (Nat.gcd_dvd_right c d)
        have hleft : q.1.1 * (a / q.1.1) * (b / q.1.1) ∣ a * b := by
          refine ⟨q.1.1, ?_⟩
          calc
            a * b = ((a / q.1.1) * q.1.1) * ((b / q.1.1) * q.1.1) := by
              rw [Nat.div_mul_cancel hr₁a, Nat.div_mul_cancel hr₁b]
            _ = (q.1.1 * (a / q.1.1) * (b / q.1.1)) * q.1.1 := by ring
        have hright : q.2.1 * (c / q.2.1) * (d / q.2.1) ∣ c * d := by
          refine ⟨q.2.1, ?_⟩
          calc
            c * d = ((c / q.2.1) * q.2.1) * ((d / q.2.1) * q.2.1) := by
              rw [Nat.div_mul_cancel hr₂c, Nat.div_mul_cancel hr₂d]
            _ = (q.2.1 * (c / q.2.1) * (d / q.2.1)) * q.2.1 := by ring
        have hq : Nat.Coprime
            (q.1.1 * (a / q.1.1) * (b / q.1.1))
            (q.2.1 * (c / q.2.1) * (d / q.2.1)) :=
          h.of_dvd_left hleft |>.of_dvd_right hright
        change shiftedSelbergCorrectionWeight s (q.1.1 * q.2.1)
            ((a * c) / (q.1.1 * q.2.1))
            ((b * d) / (q.1.1 * q.2.1)) = _
        rw [quotient_mul_quotient_eq' ha hc hr₁a hr₂c,
          quotient_mul_quotient_eq' hb hd hr₁b hr₂d,
          shiftedSelbergCorrectionWeight_mul_of_coprime s hq]
      _ = (∑ r : {r // r ∈ g₁.divisors},
            shiftedSelbergCorrectionWeight s r.1 (a / r.1) (b / r.1)) *
          ∑ r : {r // r ∈ g₂.divisors},
            shiftedSelbergCorrectionWeight s r.1 (c / r.1) (d / r.1) := by
        rw [Fintype.sum_prod_type]
        simpa only using (Fintype.sum_mul_sum
          (fun r : {r // r ∈ g₁.divisors} =>
            shiftedSelbergCorrectionWeight s r.1 (a / r.1) (b / r.1))
          (fun r : {r // r ∈ g₂.divisors} =>
            shiftedSelbergCorrectionWeight s r.1 (c / r.1) (d / r.1))).symm

theorem localizedShiftedSelbergAmplitude_prime_pow_of_dvd (s : ℝ)
    {r p i : ℕ} (hp : p.Prime) (hpr : p ∣ r) :
    localizedShiftedSelbergAmplitude s r (p ^ i) = powerShiftedReciprocalAmplitude s (p ^ i) := by
  classical
  rcases i with _ | i
  · simp
  · rw [localizedShiftedSelbergAmplitude,
      if_pos ((primeSupportedOn_prime_pow_iff hp (by omega)).2 hpr)]

theorem localizedShiftedSelbergAmplitude_prime_pow_succ_of_not_dvd (s : ℝ)
    {r p i : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) :
    localizedShiftedSelbergAmplitude s r (p ^ (i + 1)) = 0 := by
  classical
  rw [localizedShiftedSelbergAmplitude, if_neg]
  exact fun hs => hpr ((primeSupportedOn_prime_pow_iff hp (by omega)).1 hs)

/-- For a prime `p`, the Euler correction coefficient vanishes at `(p^(i+1), 1)`. -/
theorem shiftedSelbergCorrectionCoeff_prime_pow_succ_one (s : ℝ)
    {p i : ℕ} (hp : p.Prime) :
    shiftedSelbergCorrectionCoeff s (p ^ (i + 1)) 1 = 0 := by
  rw [shiftedSelbergCorrectionCoeff, if_neg (by simp [hp.ne_zero])]
  have hgcd : Nat.gcd (p ^ (i + 1)) 1 = 1 := Nat.gcd_one_right _
  rw [hgcd]
  let z₀ : {r // r ∈ (1 : ℕ).divisors} := ⟨1, by simp⟩
  rw [Fintype.sum_eq_single z₀]
  · simp [z₀, shiftedSelbergCorrectionWeight,
      localizedShiftedSelbergAmplitude_prime_pow_succ_of_not_dvd s hp hp.not_dvd_one]
  · intro z hz
    exfalso
    apply hz
    apply Subtype.ext
    exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2)

/-- For a prime `p`, the Euler correction coefficient vanishes at `(1, p^(j+1))`. -/
theorem shiftedSelbergCorrectionCoeff_one_prime_pow_succ (s : ℝ)
    {p j : ℕ} (hp : p.Prime) :
    shiftedSelbergCorrectionCoeff s 1 (p ^ (j + 1)) = 0 := by
  rw [shiftedSelbergCorrectionCoeff, if_neg (by simp [hp.ne_zero])]
  have hgcd : Nat.gcd 1 (p ^ (j + 1)) = 1 := Nat.gcd_one_left _
  rw [hgcd]
  let z₀ : {r // r ∈ (1 : ℕ).divisors} := ⟨1, by simp⟩
  rw [Fintype.sum_eq_single z₀]
  · simp [z₀, shiftedSelbergCorrectionWeight,
      localizedShiftedSelbergAmplitude_prime_pow_succ_of_not_dvd s hp hp.not_dvd_one]
  · intro z hz
    exfalso
    apply hz
    apply Subtype.ext
    exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2)

private theorem gcd_prime_pow_eq_pow_min {p i j : ℕ} :
    Nat.gcd (p ^ i) (p ^ j) = p ^ min i j := by
  rcases le_total i j with hij | hji
  · rw [min_eq_left hij, Nat.gcd_eq_left_iff_dvd.mpr (pow_dvd_pow p hij)]
  · rw [min_eq_right hji, Nat.gcd_eq_right_iff_dvd.mpr (pow_dvd_pow p hji)]

/-- For a prime `p`, `shiftedSelbergCorrectionCoeff s (p^(i+1)) (p^(j+1)) = -(1/p^2) · A(p^i) · A(p^j)`,
where `A = powerShiftedReciprocalAmplitude s`; only the divisor `r = p` of the gcd contributes. -/
theorem shiftedSelbergCorrectionCoeff_prime_pow_succ (s : ℝ)
    {p i j : ℕ} (hp : p.Prime) :
    shiftedSelbergCorrectionCoeff s (p ^ (i + 1)) (p ^ (j + 1)) =
      (-(1 : ℝ) / ((p : ℝ) ^ (2 : ℕ))) *
        powerShiftedReciprocalAmplitude s (p ^ i) * powerShiftedReciprocalAmplitude s (p ^ j) := by
  rw [shiftedSelbergCorrectionCoeff, if_neg (by simp [hp.ne_zero])]
  change (∑ r ∈ (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors.attach,
      shiftedSelbergCorrectionWeight s r.1 ((p ^ (i + 1)) / r.1)
        ((p ^ (j + 1)) / r.1)) = _
  rw [show (∑ r ∈ (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors.attach,
        shiftedSelbergCorrectionWeight s r.1 ((p ^ (i + 1)) / r.1)
          ((p ^ (j + 1)) / r.1)) =
      ∑ r ∈ (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors,
        shiftedSelbergCorrectionWeight s r ((p ^ (i + 1)) / r)
          ((p ^ (j + 1)) / r) by
      simpa only using (Finset.sum_attach
        (Nat.gcd (p ^ (i + 1)) (p ^ (j + 1))).divisors
        (fun r : ℕ => shiftedSelbergCorrectionWeight s r ((p ^ (i + 1)) / r)
          ((p ^ (j + 1)) / r)))]
  rw [gcd_prime_pow_eq_pow_min, Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_eq_single 1]
  · have hpi : p ^ (i + 1) / p ^ (1 : ℕ) = p ^ i := by
      simpa using Nat.pow_div (x := p) (m := i + 1) (n := 1) (by omega) hp.pos
    have hpj : p ^ (j + 1) / p ^ (1 : ℕ) = p ^ j := by
      simpa using Nat.pow_div (x := p) (m := j + 1) (n := 1) (by omega) hp.pos
    rw [hpi, hpj, pow_one, shiftedSelbergCorrectionWeight,
      ArithmeticFunction.moebius_apply_prime hp,
      localizedShiftedSelbergAmplitude_prime_pow_of_dvd s hp (dvd_refl p),
      localizedShiftedSelbergAmplitude_prime_pow_of_dvd s hp (dvd_refl p)]
    push_cast
    ring
  · intro k hk hk1
    have hklt : k < min (i + 1) (j + 1) + 1 := Finset.mem_range.mp hk
    rcases eq_or_ne k 0 with rfl | hk0
    · simp [shiftedSelbergCorrectionWeight,
        localizedShiftedSelbergAmplitude_prime_pow_succ_of_not_dvd s hp hp.not_dvd_one]
    · have hk2 : k ≠ 1 := by exact fun h1 => hk1 h1
      rw [shiftedSelbergCorrectionWeight,
        ArithmeticFunction.moebius_apply_prime_pow hp hk0, if_neg hk2]
      norm_num
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

end GaloisForLFunctions.MultiscaleMollifiedZetaField
