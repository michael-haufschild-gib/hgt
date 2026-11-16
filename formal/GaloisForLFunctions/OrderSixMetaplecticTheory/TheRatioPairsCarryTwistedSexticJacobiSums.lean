import GaloisForLFunctions.OrderSixMetaplecticTheory.EachFractionalTranslateCarriesTheKubotaCharacter

/-!
# The ratio pairs carry twisted sextic Jacobi sums

Character sums of the quadratic weight `λ` over the ratio pairs `(t, ct)`, `c ≠ 0, 1`, `q` odd:

* the middle cusps: `Σ_{x≢0}Σ_tλ(t)χ(Q(9tx))ψ((1 − c)tκ/Q(9tx)) = g_λλ((1 − c)κ)(J_c − 1)` with
  `Q(s) = (1 + s)(1 + cs)` and `J_c = Σ_s(χλ)(Q(s))` (`jacobi_double_sum_ratio`). Every pair whose
  phase is `χ(3x)⁻¹` times a function of `9tx` cancels (`high_sum_vanish`);
* completing the square, `J_c = (χλ)(−D)J₆`, `D = (1 − c)²/(4c)` (`ratioJacobi_eq`);
* the cusp `0`: `Σ_{x≢0}λ(x)χ(−3x)χ(−3cx)ψ((9x)⁻¹(c⁻¹ − 1)κ) = C_c Σ_u(χλ)(u)ψ(uκ)`,
  `C_c = χ(9c)λ(M)χ(M)²`, `M = (1 − c)/(9c)` (`gauss_low_sum_ratio`);
* **the two coefficients of every ratio are proportional to those of the opposite pairs**:
  `λ(1 − c)J_c · C_{−1} = λ(2)J₆ · C_c` (`ratio_coefficients_proportional`). The proof only uses
  `(1 − c)(−D)(−2) = 2M·(3(1 − c)/2)²` and `(−D)(−4) = 9c·M²·9`.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem lam_mul_sq (x z : P.Res) (hz : z ≠ 0) : P.lam (x * z ^ 2) = P.lam x := by
  rw [map_mul, map_pow, P.lam_sq z hz, mul_one]

theorem chi_neg_one : P.chi (-1) = 1 := by
  have h3 := P.chi_cube (-1) (neg_ne_zero.mpr one_ne_zero)
  have h2 : P.chi (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, MulChar.map_one]
  calc P.chi (-1) = P.chi (-1) * P.chi (-1) ^ 2 := by rw [h2, mul_one]
    _ = P.chi (-1) ^ 3 := by ring
    _ = 1 := h3

/-- For `x ≠ 0`: `Σ_tλ(t)g(9tx) = λ(9x)Σ_sλ(s)g(s)`. -/
theorem sum_lam_scale (x : P.Res) (hx : x ≠ 0) (g : P.Res → ℂ) :
    ∑ t : P.Res, P.lam t * g (9 * t * x) = P.lam (9 * x) * ∑ s : P.Res, P.lam s * g s := by
  have h9 := P.nine_ne_zero'
  have hx9 : 9 * x ≠ 0 := mul_ne_zero h9 hx
  rw [← (mulRight_bijective₀ (9 * x)⁻¹ (inv_ne_zero hx9)).sum_comp (fun t => P.lam t * g (9 * t * x)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show 9 * (s * (9 * x)⁻¹) * x = s by field_simp, map_mul, P.mulChar_inv_apply _ _ hx9, P.lam_inv _ hx9]
  ring

/-- **The high pairs cancel against `λ`.** -/
theorem high_sum_vanish (h2 : (2 : P.Res) ≠ 0) (g : P.Res → ℂ) :
    ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * ((P.chi (3 * x.1))⁻¹ * g (9 * t * x.1)) = 0 := by
  have e : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * ((P.chi (3 * x.1))⁻¹ * g (9 * t * x.1)) =
      ((P.chi (3 * x.1))⁻¹ * P.lam (9 * x.1)) * ∑ s : P.Res, P.lam s * g s := by
    intro x
    have h := P.sum_lam_scale x.1 x.2 (fun s => (P.chi (3 * x.1))⁻¹ * g s)
    rw [h, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  simp_rw [e]
  rw [← Finset.sum_mul]
  have hz1 : ∑ x : {x : P.Res // x ≠ 0}, (P.chi (3 * x.1))⁻¹ * P.lam (9 * x.1) = 0 := by
    rw [P.sum_ne_zero_eq (fun x => (P.chi (3 * x))⁻¹ * P.lam (9 * x))]
    have : ∑ x : P.Res, (P.chi (3 * x))⁻¹ * P.lam (9 * x) =
        (P.chi ^ 2) 3 * P.lam 9 * ∑ x : P.Res, (P.chi ^ 2) x * P.lam x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [P.chi_inv_eq, map_mul, map_mul]
      ring
    rw [this, P.chiSq_lam_sum h2]
    simp [MulChar.map_zero]
  rw [hz1, zero_mul]

/-- `J_c = Σ_s(χλ)((1 + s)(1 + cs))`. -/
def ratioJacobi (c : P.Res) : ℂ :=
  ∑ s : P.Res, P.chi ((1 + s) * (1 + c * s)) * P.lam ((1 + s) * (1 + c * s))

/-- **The middle-cusp phases of the ratio pairs.** -/
theorem jacobi_double_sum_ratio (h2 : (2 : P.Res) ≠ 0) (c κ : P.Res) :
    ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
        (P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
          P.traceChar ((1 - c) * t / ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) * κ)) =
      gaussSum P.lam P.traceChar * P.lam ((1 - c) * κ) * (P.ratioJacobi c - 1) := by
  have h9 := P.nine_ne_zero'
  set G := gaussSum P.lam P.traceChar with hG
  set f : P.Res → P.Res → ℂ := fun s t =>
    P.chi ((1 + s) * (1 + c * s)) * P.traceChar ((1 - c) * t / ((1 + s) * (1 + c * s)) * κ) with hf
  have hstep4 : ∀ t : P.Res, P.lam t * ∑ x : P.Res, f (9 * t * x) t = P.lam t * ∑ s : P.Res, f s t := by
    intro t
    by_cases ht : t = 0
    · rw [ht, MulChar.map_zero, zero_mul, zero_mul]
    · exact congrArg (P.lam t * ·) ((mulLeft_bijective₀ (9 * t) (mul_ne_zero h9 ht)).sum_comp (fun s => f s t))
  have hstep3 : ∑ t : P.Res, P.lam t * f (9 * t * 0) t = P.lam ((1 - c) * κ) * G := by
    rw [hG, ← P.sum_lam_traceChar h2 ((1 - c) * κ)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hf, mul_zero, add_zero, mul_one, MulChar.map_one, one_mul, div_one]
    congr 2
    ring
  have hstep56 : ∀ s : P.Res, ∑ t : P.Res, P.lam t * f s t =
      G * P.lam ((1 - c) * κ) * (P.chi ((1 + s) * (1 + c * s)) * P.lam ((1 + s) * (1 + c * s))) := by
    intro s
    by_cases hs : (1 + s) * (1 + c * s) = 0
    · simp only [hf, hs, MulChar.map_zero, zero_mul, mul_zero, Finset.sum_const_zero]
    · have e : ∀ t, P.lam t * f s t = P.chi ((1 + s) * (1 + c * s)) *
          (P.lam t * P.traceChar (t * ((1 - c) * κ * ((1 + s) * (1 + c * s))⁻¹))) := by
        intro t
        simp only [hf]
        rw [show (1 - c) * t / ((1 + s) * (1 + c * s)) * κ = t * ((1 - c) * κ * ((1 + s) * (1 + c * s))⁻¹) by ring]
        ring
      rw [Finset.sum_congr rfl (fun t _ => e t), ← Finset.mul_sum, P.sum_lam_traceChar h2,
        map_mul P.lam ((1 - c) * κ), P.mulChar_inv_apply _ _ hs, P.lam_inv _ hs, hG]
      ring
  have hL : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
      (P.chi ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) *
        P.traceChar ((1 - c) * t / ((1 + 9 * t * x.1) * (1 + c * (9 * t * x.1))) * κ)) =
      ∑ x : {x : P.Res // x ≠ 0}, (fun x => ∑ t : P.Res, P.lam t * f (9 * t * x) t) x.1 := rfl
  rw [hL, P.sum_ne_zero_eq (fun x => ∑ t : P.Res, P.lam t * f (9 * t * x) t), hstep3]
  show (∑ x : P.Res, ∑ t : P.Res, P.lam t * f (9 * t * x) t) - P.lam ((1 - c) * κ) * G = _
  rw [Finset.sum_comm]
  have hfull : ∑ t : P.Res, ∑ x : P.Res, P.lam t * f (9 * t * x) t = ∑ s : P.Res, G * P.lam ((1 - c) * κ) *
      (P.chi ((1 + s) * (1 + c * s)) * P.lam ((1 + s) * (1 + c * s))) := by
    simp_rw [← Finset.mul_sum]
    simp_rw [hstep4]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => by rw [← hstep56 s]
  rw [hfull, ← Finset.mul_sum, ratioJacobi]
  ring

/-- **Completing the square**: `J_c = (χλ)(−D)J₆`, `D = (1 − c)²/(4c)`. -/
theorem ratioJacobi_eq (h2 : (2 : P.Res) ≠ 0) (c : P.Res) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    P.ratioJacobi c = P.chi (-((1 - c) ^ 2 / (4 * c))) * P.lam (-((1 - c) ^ 2 / (4 * c))) * P.lamJacobi := by
  have h1c : (1 : P.Res) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have hf : (1 - c) / (2 * c) ≠ 0 := div_ne_zero h1c (mul_ne_zero h2 hc0)
  have h4 : (4 : P.Res) ≠ 0 := by rw [show (4 : P.Res) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have key : ∀ s : P.Res, (1 + s) * (1 + c * s) =
      -((1 - c) ^ 2 / (4 * c)) * (1 - ((s + (1 + c) / (2 * c)) * ((1 - c) / (2 * c))⁻¹) ^ 2) := by
    intro s
    field_simp
    ring
  have hb : Function.Bijective (fun s : P.Res => (s + (1 + c) / (2 * c)) * ((1 - c) / (2 * c))⁻¹) :=
    (mulRight_bijective₀ _ (inv_ne_zero hf)).comp (Equiv.addRight ((1 + c) / (2 * c))).bijective
  unfold ratioJacobi lamJacobi
  simp_rw [key, map_mul]
  rw [Finset.mul_sum]
  rw [← hb.sum_comp (fun u => P.chi (-((1 - c) ^ 2 / (4 * c))) * P.lam (-((1 - c) ^ 2 / (4 * c))) *
    (P.chi (1 - u ^ 2) * P.lam (1 - u ^ 2)))]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- The cusp-0 coefficient `C_c = χ(9c)λ(M)χ(M)²`, `M = (1 − c)/(9c)`. -/
def cuspZeroCoeff (c : P.Res) : ℂ :=
  P.chi (9 * c) * P.lam ((1 - c) / (9 * c)) * P.chi ((1 - c) / (9 * c)) ^ 2

/-- **The cusp-0 phases of the ratio pairs are a sextic Gauss sum.** -/
theorem gauss_low_sum_ratio (c : P.Res) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (κ : P.Res) :
    ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-3 * x.1) * P.chi (-3 * (c * x.1)) *
        P.traceChar ((9 * x.1)⁻¹ * (c⁻¹ - 1) * κ)) =
      P.cuspZeroCoeff c * ∑ u : P.Res, P.chi u * P.lam u * P.traceChar (u * κ) := by
  have h9 := P.nine_ne_zero'
  have h1c : (1 : P.Res) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  set M : P.Res := (1 - c) / (9 * c) with hM
  have hM0 : M ≠ 0 := div_ne_zero h1c (mul_ne_zero h9 hc0)
  set σ : P.Res → P.Res := fun y => M * y⁻¹ with hσ
  have hinv : Function.Involutive σ := by
    intro y
    by_cases hy : y = 0
    · simp [hσ, hy]
    · simp only [hσ]
      field_simp
  set F : P.Res → ℂ := fun x => P.lam x * (P.chi (-3 * x) * P.chi (-3 * (c * x)) *
    P.traceChar ((9 * x)⁻¹ * (c⁻¹ - 1) * κ)) with hF
  have hfull : ∑ x : P.Res, F x = P.cuspZeroCoeff c * ∑ u : P.Res, P.chi u * P.lam u * P.traceChar (u * κ) := by
    rw [← hinv.bijective.sum_comp F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y = 0
    · simp [hF, hσ, hy, MulChar.map_zero]
    · have hph : (9 * σ y)⁻¹ * (c⁻¹ - 1) * κ = y * κ := by
        simp only [hσ, hM]
        field_simp
      have hl : P.lam (σ y) = P.lam M * P.lam y := by
        simp only [hσ]
        rw [map_mul, P.mulChar_inv_apply _ _ hy, P.lam_inv _ hy]
      have hc : P.chi (-3 * σ y) * P.chi (-3 * (c * σ y)) = P.chi (9 * c) * P.chi M ^ 2 * P.chi y := by
        simp only [hσ]
        rw [← map_mul, show -3 * (M * y⁻¹) * (-3 * (c * (M * y⁻¹))) = 9 * c * M ^ 2 * y⁻¹ ^ 2 by ring,
          map_mul, map_mul, map_pow, map_pow, P.mulChar_inv_apply _ _ hy, P.chi_inv_sq y hy]
      simp only [hF]
      rw [hph, hl, hc, cuspZeroCoeff]
      ring
  rw [P.sum_ne_zero_eq F, hfull]
  simp [hF, MulChar.map_zero]

theorem cuspZeroCoeff_neg_one :
    P.cuspZeroCoeff (-1) = P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2) := by
  have h9 := P.nine_ne_zero'
  have h3 := P.three_ne_zero'
  have hl9 : P.lam 9 = 1 := by rw [show (9 : P.Res) = 3 ^ 2 by norm_num, map_pow, P.lam_sq 3 h3]
  have hc9 : P.chi (-9) = P.chi 9 := by
    rw [show (-9 : P.Res) = -1 * 9 by ring, map_mul, P.chi_neg_one, one_mul]
  have hc4 : P.chi (-4) = P.chi (-2) ^ 2 := by
    rw [show (-4 : P.Res) = -1 * (-2) ^ 2 by ring, map_mul, map_pow, P.chi_neg_one, one_mul]
  have hχ9 : P.chi 9 ≠ 0 := P.chi_ne_zero_of_ne _ h9
  unfold cuspZeroCoeff
  rw [show (9 : P.Res) * -1 = -9 by ring, show ((1 : P.Res) - -1) / (-9) = -2 * 9⁻¹ by field_simp; ring, hc9, hc4,
    map_mul P.lam, P.mulChar_inv_apply _ _ h9, hl9, inv_one, mul_one, map_mul P.chi,
    P.mulChar_inv_apply _ _ h9]
  field_simp

/-- **Rigidity of the ratio pairs.** For `c ≠ 0, 1` the two coefficients of the ratio pairs are
proportional to those of the opposite pairs: `λ(1 − c)J_c · C_{−1} = λ(2)J₆ · C_c`. -/
theorem ratio_coefficients_proportional (h2 : (2 : P.Res) ≠ 0) (c : P.Res) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    P.lam (1 - c) * P.ratioJacobi c * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2)) =
      P.lam 2 * P.lamJacobi * P.cuspZeroCoeff c := by
  have h9 := P.nine_ne_zero'
  have h1c : (1 : P.Res) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have h4 : (4 : P.Res) ≠ 0 := by rw [show (4 : P.Res) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hz : (3 * (1 - c) / 2 : P.Res) ≠ 0 := div_ne_zero (mul_ne_zero P.three_ne_zero' h1c) h2
  set D : P.Res := (1 - c) ^ 2 / (4 * c) with hD
  set M : P.Res := (1 - c) / (9 * c) with hM
  have hlam : P.lam (1 - c) * P.lam (-D) * P.lam (-2) = P.lam 2 * P.lam M := by
    rw [← map_mul P.lam, ← map_mul P.lam, ← map_mul P.lam,
      show (1 - c) * -D * -2 = 2 * M * (3 * (1 - c) / 2) ^ 2 by simp only [hD, hM]; field_simp; ring,
      P.lam_mul_sq _ _ hz]
  have hchi : P.chi (-D) * P.chi (-4) = P.chi (9 * c) * P.chi M ^ 2 * P.chi 9 := by
    rw [← map_mul P.chi, ← map_pow P.chi, ← map_mul P.chi, ← map_mul P.chi,
      show -D * -4 = 9 * c * M ^ 2 * 9 by simp only [hD, hM]; field_simp]
  have h9c : P.chi 9 ≠ 0 := P.chi_ne_zero_of_ne _ h9
  rw [P.ratioJacobi_eq h2 c hc0 hc1, cuspZeroCoeff, ← hD, ← hM]
  calc P.lam (1 - c) * (P.chi (-D) * P.lam (-D) * P.lamJacobi) * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2)) =
        P.lamJacobi * (P.lam (1 - c) * P.lam (-D) * P.lam (-2)) * (P.chi (-D) * P.chi (-4)) * (P.chi 9)⁻¹ := by ring
    _ = P.lamJacobi * (P.lam 2 * P.lam M) * (P.chi (9 * c) * P.chi M ^ 2 * P.chi 9) * (P.chi 9)⁻¹ := by
        rw [hlam, hchi]
    _ = P.lam 2 * P.lamJacobi * (P.chi (9 * c) * P.lam M * P.chi M ^ 2) := by
        field_simp

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
