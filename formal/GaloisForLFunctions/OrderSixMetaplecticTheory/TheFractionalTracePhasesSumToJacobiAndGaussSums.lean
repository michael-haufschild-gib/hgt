import GaloisForLFunctions.OrderSixMetaplecticTheory.TheMiddleCuspsOfTheFractionalTraceCarryJacobiPhases

/-!
# The phases of the fractional trace sum to Jacobi and Gauss sums

Finite-field identities in `O/q` (q odd, χ = (·/q)₃, ψ the principal trace character) that evaluate the
phases of the fractional trace:

* the middle cusps (s = 9tx): Σ_{x≢0} Σ_t χ(1 − s²) ψ(2tκ/(1 − s²)) = N − J + (J − 1)N[κ = 0]
  (`jacobi_double_sum`), with the **Jacobi sum** J = Σ_s χ(1 − s²) of χ and the quadratic character
  (`fracJacobi`); in particular Σ_{x≢0} Σ_t χ(1 − s²) = (N − 1)J (`jacobi_double_count`);
* the cusp 0: Σ_x χ(−9x²) ψ(−2κ/(9x)) = χ(−4)χ(9)⁻¹ Σ_u χ(u)ψ(uκ), a cubic Gauss sum (`gauss_low_sum`);
* the high points and the low–low phases cancel: Σ_{x≢0} χ(3x)⁻¹ = 0, Σ_x χ(−9x²) = 0.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- The principal trace character of O/q. -/
abbrev traceChar : AddChar P.Res ℂ := principalTraceChar P.p P.ne_zero

/-- The Jacobi sum J = Σ_s χ(1 − s²) of the cubic and the quadratic character of O/q. -/
def fracJacobi : ℂ := ∑ s : P.Res, P.chi (1 - s ^ 2)

/-- |O/q| = N(q) in ℂ. -/
abbrev normC : ℂ := (Fintype.card P.Res : ℂ)

theorem sum_traceChar_mul (c : P.Res) :
    ∑ t : P.Res, P.traceChar (t * c) = if c = 0 then P.normC else 0 := by
  rw [AddChar.sum_mulShift _ (principalTraceChar_primitive P.p P.ne_zero)]
  split_ifs <;> simp [normC]

theorem sum_ne_zero_eq (f : P.Res → ℂ) : ∑ x : {x : P.Res // x ≠ 0}, f x.1 = ∑ x : P.Res, f x - f 0 := by
  rw [Fintype.sum_eq_add_sum_compl (0 : P.Res) f,
    Finset.sum_subtype _ (fun x => by simp : ∀ x, x ∈ ({0}ᶜ : Finset P.Res) ↔ x ≠ 0)]
  ring

theorem chi_ne_zero_of_ne (u : P.Res) (hu : u ≠ 0) : P.chi u ≠ 0 := by
  intro h0
  have h := P.chi_cube u hu
  rw [h0] at h
  norm_num at h

theorem chi_inv_eq_sq (u : P.Res) (hu : u ≠ 0) : (P.chi u)⁻¹ = P.chi u ^ 2 :=
  (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact P.chi_cube u hu)).symm

theorem chi_inv_sq (u : P.Res) (hu : u ≠ 0) : (P.chi u)⁻¹ ^ 2 = P.chi u := by
  rw [P.chi_inv_eq_sq u hu, ← pow_mul]
  linear_combination (P.chi u) * P.chi_cube u hu

theorem chi_sq_ne_one : P.chi ^ 2 ≠ 1 := by
  intro h
  apply P.chi_ne_one
  have h3 : P.chi ^ 3 = 1 := primeCubicMulChar_cube P.p P.prime P.primary
  calc P.chi = P.chi ^ 3 * (P.chi ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h, inv_one, mul_one]

/-- **The middle-cusp phases.** Σ_{x ≢ 0} Σ_t χ(1 − s²) ψ(2tκ/(1 − s²)) = N − J + (J − 1)N[κ = 0], s = 9tx. -/
theorem jacobi_double_sum (h2 : (2 : P.Res) ≠ 0) (κ : P.Res) :
    ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res,
        P.chi (1 - (9 * t * x.1) ^ 2) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * κ) =
      P.normC - P.fracJacobi + (P.fracJacobi - 1) * (if κ = 0 then P.normC else 0) := by
  have h9 := P.nine_ne_zero'
  set f : P.Res → P.Res → ℂ := fun s t => P.chi (1 - s ^ 2) * P.traceChar (2 * t / (1 - s ^ 2) * κ) with hf
  have hall : ∑ x : P.Res, ∑ t : P.Res, f (9 * t * x) t =
      P.normC + P.fracJacobi * ((if κ = 0 then P.normC else 0) - 1) := by
    rw [Finset.sum_comm, Fintype.sum_eq_add_sum_compl (0 : P.Res)]
    have h0 : ∑ x : P.Res, f (9 * 0 * x) 0 = P.normC := by
      simp [hf, Finset.card_univ]
    have hne : ∀ t ∈ ({0}ᶜ : Finset P.Res), ∑ x : P.Res, f (9 * t * x) t = ∑ s : P.Res, f s t := by
      intro t ht
      have ht0 : t ≠ 0 := by simpa using ht
      exact (mulLeft_bijective₀ (9 * t) (mul_ne_zero h9 ht0)).sum_comp (fun s => f s t)
    rw [h0, Finset.sum_congr rfl hne, Finset.sum_comm]
    congr 1
    rw [fracJacobi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hf]
    rw [← Finset.mul_sum]
    by_cases hs : 1 - s ^ 2 = 0
    · rw [hs, MulChar.map_zero, zero_mul, zero_mul]
    · congr 1
      have hfull := P.sum_traceChar_mul (2 / (1 - s ^ 2) * κ)
      rw [Fintype.sum_eq_add_sum_compl (0 : P.Res)] at hfull
      simp only [zero_mul, AddChar.map_zero_eq_one] at hfull
      have hc : (2 / (1 - s ^ 2) * κ = 0) ↔ κ = 0 := by
        constructor
        · intro h
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' (div_ne_zero h2 hs)
          · exact h'
        · intro h
          rw [h, mul_zero]
      have e : ∀ t, P.traceChar (2 * t / (1 - s ^ 2) * κ) = P.traceChar (t * (2 / (1 - s ^ 2) * κ)) := by
        intro t
        congr 1
        ring
      simp_rw [e]
      rw [if_congr hc rfl rfl] at hfull
      linear_combination hfull
  have hzero : ∑ t : P.Res, f (9 * t * 0) t = if κ = 0 then P.normC else 0 := by
    simp only [hf, mul_zero, zero_pow two_ne_zero, sub_zero, MulChar.map_one, one_mul, div_one]
    have := P.sum_traceChar_mul (2 * κ)
    have hc : (2 * κ = 0) ↔ κ = 0 := ⟨fun h => (mul_eq_zero.mp h).resolve_left h2, fun h => by rw [h, mul_zero]⟩
    rw [if_congr hc rfl rfl] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hsplit : ∑ x : P.Res, ∑ t : P.Res, f (9 * t * x) t =
      ∑ t : P.Res, f (9 * t * 0) t + ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, f (9 * t * x.1) t := by
    rw [Fintype.sum_eq_add_sum_compl (0 : P.Res),
      Finset.sum_subtype _ (fun x => by simp : ∀ x, x ∈ ({0}ᶜ : Finset P.Res) ↔ x ≠ 0)]
  rw [hsplit, hzero] at hall
  show ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, f (9 * t * x.1) t = _
  linear_combination hall

/-- **The main-term count.** Σ_{x ≢ 0} Σ_t χ(1 − (9tx)²) = (N − 1)J. -/
theorem jacobi_double_count :
    ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.chi (1 - (9 * t * x.1) ^ 2) = (P.normC - 1) * P.fracJacobi := by
  have h9 := P.nine_ne_zero'
  have hx : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.chi (1 - (9 * t * x.1) ^ 2) = P.fracJacobi := by
    intro x
    have h := (mulRight_bijective₀ (9 * x.1) (mul_ne_zero h9 x.2)).sum_comp (fun s => P.chi (1 - s ^ 2))
    rw [fracJacobi, ← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hc : Fintype.card {x : P.Res // x ≠ 0} = Fintype.card P.Res - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
    Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-- (χ u)⁻¹ = χ²(u). -/
theorem chi_inv_eq (u : P.Res) : (P.chi u)⁻¹ = (P.chi ^ 2) u := by
  by_cases hu : u = 0
  · rw [hu, MulChar.map_zero, inv_zero, MulChar.map_zero]
  · rw [MulChar.pow_apply' _ (by norm_num), P.chi_inv_eq_sq u hu]

/-- The high phases cancel: Σ_{x ≢ 0} χ(3x)⁻¹ = 0. -/
theorem sum_chi_three_inv : ∑ x : {x : P.Res // x ≠ 0}, (P.chi (3 * x.1))⁻¹ = 0 := by
  have h3 := P.three_ne_zero'
  have hfull : ∑ x : P.Res, (P.chi (3 * x))⁻¹ = 0 := by
    rw [(mulLeft_bijective₀ (3 : P.Res) h3).sum_comp (fun u => (P.chi u)⁻¹)]
    simp_rw [P.chi_inv_eq]
    exact MulChar.sum_eq_zero_of_ne_one P.chi_sq_ne_one
  rw [P.sum_ne_zero_eq (fun x => (P.chi (3 * x))⁻¹), hfull]
  simp [MulChar.map_zero]

/-- The low–low phases cancel: Σ_{x ≢ 0} χ(−9x²) = 0. -/
theorem sum_chi_low : ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) = 0 := by
  have hfull : ∑ x : P.Res, P.chi (-9 * x ^ 2) = 0 := by
    simp_rw [map_mul, map_pow, ← Finset.mul_sum]
    have : ∀ u : P.Res, P.chi u ^ 2 = (P.chi ^ 2) u := fun u => by rw [MulChar.pow_apply' _ (by norm_num)]
    simp_rw [this]
    rw [MulChar.sum_eq_zero_of_ne_one P.chi_sq_ne_one, mul_zero]
  rw [P.sum_ne_zero_eq (fun x => P.chi (-9 * x ^ 2)), hfull]
  simp [MulChar.map_zero]

/-- **The cusp-0 phases are a cubic Gauss sum.** Σ_{x ≢ 0} χ(−9x²)ψ(−2κ/(9x)) = χ(−4)χ(9)⁻¹ Σ_u χ(u)ψ(uκ). -/
theorem gauss_low_sum (h2 : (2 : P.Res) ≠ 0) (κ : P.Res) :
    ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) * P.traceChar (-2 * (9 * x.1)⁻¹ * κ) =
      P.chi (-4) * (P.chi 9)⁻¹ * ∑ u : P.Res, P.chi u * P.traceChar (u * κ) := by
  have h9 := P.nine_ne_zero'
  have hinvχ : ∀ a : P.Res, a ≠ 0 → P.chi a⁻¹ = (P.chi a)⁻¹ := fun a ha =>
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ ha, MulChar.map_one])
  set σ : P.Res → P.Res := fun x => -2 * (9 * x)⁻¹ with hσ
  have hinv : Function.Involutive σ := by
    intro x
    by_cases hx : x = 0
    · simp [hσ, hx]
    · simp only [hσ]
      field_simp
  have hfull : ∑ x : P.Res, P.chi (-9 * x ^ 2) * P.traceChar (σ x * κ) =
      P.chi (-4) * (P.chi 9)⁻¹ * ∑ u : P.Res, P.chi u * P.traceChar (u * κ) := by
    rw [← hinv.bijective.sum_comp (fun x => P.chi (-9 * x ^ 2) * P.traceChar (σ x * κ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hinv u]
    by_cases hu : u = 0
    · simp [hσ, hu, MulChar.map_zero]
    · have e : -9 * σ u ^ 2 = (-4) * 9⁻¹ * u⁻¹ ^ 2 := by
        simp only [hσ]
        field_simp
        ring
      rw [e, map_mul, map_mul, map_pow, hinvχ 9 h9, hinvχ u hu, P.chi_inv_sq u hu]
      ring
  rw [P.sum_ne_zero_eq (fun x => P.chi (-9 * x ^ 2) * P.traceChar (σ x * κ)), hfull]
  simp [MulChar.map_zero]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
