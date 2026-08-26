import GaloisForLFunctions.RHTower.Sieve.BivariateMultiplicative

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

/-!
# Coefficient form of the Barban--Vehov Euler correction

Push the absolutely summable squarefree-support correction along
`(r,u,v) ↦ (r*u,r*v)`.  Pair-coprime multiplicativity is proved at coefficient level.
-/

namespace RHTower.Sieve

noncomputable section

theorem primeSupportedOn_mul_iff_of_coprime
    {r₁ r₂ u₁ u₂ : ℕ} (h : Nat.Coprime (r₁ * u₁) (r₂ * u₂)) :
    primeSupportedOn (r₁ * r₂) (u₁ * u₂) ↔
      primeSupportedOn r₁ u₁ ∧ primeSupportedOn r₂ u₂ := by
  constructor
  · intro hs
    constructor
    · intro p hp hpu₁
      rcases hp.dvd_mul.mp (hs p hp (dvd_mul_of_dvd_left hpu₁ u₂)) with hpr₁ | hpr₂
      · exact hpr₁
      · have hpp : Nat.Coprime p p :=
          h.of_dvd_left (dvd_mul_of_dvd_right hpu₁ r₁)
            |>.of_dvd_right (dvd_mul_of_dvd_left hpr₂ u₂)
        exact (hp.ne_one (hpp.eq_one_of_dvd (dvd_refl p))).elim
    · intro p hp hpu₂
      rcases hp.dvd_mul.mp (hs p hp (dvd_mul_of_dvd_right hpu₂ u₁)) with hpr₁ | hpr₂
      · have hpp : Nat.Coprime p p :=
          h.of_dvd_left (dvd_mul_of_dvd_left hpr₁ u₁)
            |>.of_dvd_right (dvd_mul_of_dvd_right hpu₂ r₂)
        exact (hp.ne_one (hpp.eq_one_of_dvd (dvd_refl p))).elim
      · exact hpr₂
  · rintro ⟨hs₁, hs₂⟩ p hp hpdiv
    rcases hp.dvd_mul.mp hpdiv with hpu₁ | hpu₂
    · exact dvd_mul_of_dvd_left (hs₁ p hp hpu₁) r₂
    · exact dvd_mul_of_dvd_right (hs₂ p hp hpu₂) r₁

theorem localizedReciprocalMoebiusAmplitude_mul_of_coprime
    {r₁ r₂ u₁ u₂ : ℕ} (h : Nat.Coprime (r₁ * u₁) (r₂ * u₂)) :
    localizedReciprocalMoebiusAmplitude (r₁ * r₂) (u₁ * u₂) =
      localizedReciprocalMoebiusAmplitude r₁ u₁ *
        localizedReciprocalMoebiusAmplitude r₂ u₂ := by
  classical
  have hu : Nat.Coprime u₁ u₂ :=
    h.of_dvd_left (dvd_mul_of_dvd_right (dvd_refl u₁) r₁)
      |>.of_dvd_right (dvd_mul_of_dvd_right (dvd_refl u₂) r₂)
  have hamp := isMultiplicative_reciprocalMoebiusAmplitude.map_mul_of_coprime hu
  rw [show localizedReciprocalMoebiusAmplitude (r₁ * r₂) (u₁ * u₂) =
      if primeSupportedOn (r₁ * r₂) (u₁ * u₂) then
        reciprocalMoebiusAmplitude (u₁ * u₂) else 0 by
      rfl,
    show localizedReciprocalMoebiusAmplitude r₁ u₁ =
      if primeSupportedOn r₁ u₁ then reciprocalMoebiusAmplitude u₁ else 0 by
      rfl,
    show localizedReciprocalMoebiusAmplitude r₂ u₂ =
      if primeSupportedOn r₂ u₂ then reciprocalMoebiusAmplitude u₂ else 0 by
      rfl,
    primeSupportedOn_mul_iff_of_coprime h, hamp]
  by_cases h₁ : primeSupportedOn r₁ u₁ <;>
    by_cases h₂ : primeSupportedOn r₂ u₂ <;> simp [h₁, h₂]

theorem selbergCorrectionWeight_mul_of_coprime
    {r₁ r₂ u₁ u₂ v₁ v₂ : ℕ}
    (h : Nat.Coprime (r₁ * u₁ * v₁) (r₂ * u₂ * v₂)) :
    selbergCorrectionWeight (r₁ * r₂) (u₁ * u₂) (v₁ * v₂) =
      selbergCorrectionWeight r₁ u₁ v₁ * selbergCorrectionWeight r₂ u₂ v₂ := by
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
  rw [selbergCorrectionWeight, selbergCorrectionWeight, selbergCorrectionWeight,
    localizedReciprocalMoebiusAmplitude_mul_of_coprime hu,
    localizedReciprocalMoebiusAmplitude_mul_of_coprime hv, hmu]
  push_cast
  ring

theorem gcd_pair_mul_of_pair_coprime {a b c d : ℕ}
    (h : Nat.Coprime (a * b) (c * d)) :
    Nat.gcd (a * c) (b * d) = Nat.gcd a b * Nat.gcd c d := by
  have hac : Nat.Coprime a c :=
    (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_right c d)
  have had : Nat.Coprime a d :=
    (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_left d c)
  have hbc : Nat.Coprime b c :=
    (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_right c d)
  have hbd : Nat.Coprime b d :=
    (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_left d c)
  calc
    Nat.gcd (a * c) (b * d) =
        Nat.gcd (a * c) b * Nat.gcd (a * c) d := hbd.gcd_mul (a * c)
    _ = (Nat.gcd a b * Nat.gcd c b) *
        (Nat.gcd a d * Nat.gcd c d) := by
      rw [hac.mul_gcd b, hac.mul_gcd d]
    _ = Nat.gcd a b * Nat.gcd c d := by
      rw [show Nat.gcd c b = 1 from hbc.symm,
        show Nat.gcd a d = 1 from had]
      simp

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
def selbergEulerCorrectionCoeff (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else
    ∑ r : {r // r ∈ (Nat.gcd m n).divisors},
      selbergCorrectionWeight r.1 (m / r.1) (n / r.1)

@[simp] theorem selbergEulerCorrectionCoeff_one :
    selbergEulerCorrectionCoeff 1 1 = 1 := by
  let z₀ : {r // r ∈ (Nat.gcd 1 1).divisors} := ⟨1, by simp⟩
  rw [selbergEulerCorrectionCoeff, if_neg (by simp), Fintype.sum_eq_single z₀]
  · simp [z₀, selbergCorrectionWeight, localizedReciprocalMoebiusAmplitude]
  · intro z hz
    exfalso
    apply hz
    apply Subtype.ext
    exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2)

/-- The pushed Euler correction is bivariate multiplicative. -/
theorem bivariateMultiplicative_selbergEulerCorrectionCoeff :
    BivariateMultiplicative selbergEulerCorrectionCoeff := by
  constructor
  · exact selbergEulerCorrectionCoeff_one
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · rcases Nat.mul_eq_zero.mp hab0 with rfl | rfl <;>
        simp [selbergEulerCorrectionCoeff]
    by_cases hcd0 : c * d = 0
    · rcases Nat.mul_eq_zero.mp hcd0 with rfl | rfl <;>
        simp [selbergEulerCorrectionCoeff]
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
    simp only [selbergEulerCorrectionCoeff,
      if_neg (not_or_intro (Nat.mul_ne_zero ha.ne' hc.ne')
        (Nat.mul_ne_zero hb.ne' hd.ne')),
      if_neg (not_or_intro ha.ne' hb.ne'),
      if_neg (not_or_intro hc.ne' hd.ne')]
    rw [gcd_pair_mul_of_pair_coprime h]
    change (∑ r : {r // r ∈ (g₁ * g₂).divisors},
        selbergCorrectionWeight r.1 ((a * c) / r.1) ((b * d) / r.1)) = _
    calc
      (∑ r : {r // r ∈ (g₁ * g₂).divisors},
          selbergCorrectionWeight r.1 ((a * c) / r.1) ((b * d) / r.1)) =
          ∑ q : ({r // r ∈ g₁.divisors} × {r // r ∈ g₂.divisors}),
            selbergCorrectionWeight (e q).1
              ((a * c) / (e q).1) ((b * d) / (e q).1) := by
        exact (e.sum_comp (fun r => selbergCorrectionWeight r.1
          ((a * c) / r.1) ((b * d) / r.1))).symm
      _ = ∑ q : ({r // r ∈ g₁.divisors} × {r // r ∈ g₂.divisors}),
          selbergCorrectionWeight q.1.1 (a / q.1.1) (b / q.1.1) *
            selbergCorrectionWeight q.2.1 (c / q.2.1) (d / q.2.1) := by
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
        change selbergCorrectionWeight (q.1.1 * q.2.1)
            ((a * c) / (q.1.1 * q.2.1))
            ((b * d) / (q.1.1 * q.2.1)) = _
        rw [quotient_mul_quotient_eq' ha hc hr₁a hr₂c,
          quotient_mul_quotient_eq' hb hd hr₁b hr₂d,
          selbergCorrectionWeight_mul_of_coprime hq]
      _ = (∑ r : {r // r ∈ g₁.divisors},
            selbergCorrectionWeight r.1 (a / r.1) (b / r.1)) *
          ∑ r : {r // r ∈ g₂.divisors},
            selbergCorrectionWeight r.1 (c / r.1) (d / r.1) := by
        rw [Fintype.sum_prod_type]
        simpa only using (Fintype.sum_mul_sum
          (fun r : {r // r ∈ g₁.divisors} =>
            selbergCorrectionWeight r.1 (a / r.1) (b / r.1))
          (fun r : {r // r ∈ g₂.divisors} =>
            selbergCorrectionWeight r.1 (c / r.1) (d / r.1))).symm

end

end RHTower.Sieve
