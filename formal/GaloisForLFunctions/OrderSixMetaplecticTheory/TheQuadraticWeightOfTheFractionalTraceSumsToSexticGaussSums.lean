import GaloisForLFunctions.OrderSixMetaplecticTheory.TheWeightedFractionalTraceIsInvariantUnderTheModularGroup

/-!
# The quadratic weight of the fractional trace sums to sextic Gauss sums

The weighted fractional trace over the projective line modulo q² (`fracTraceW_eq`), the cusp 0 of the weighted
sum (`fracSumW_sO`), and the finite-field sums of the quadratic weight λ = λ_q (q odd):

* the cusp ∞: Σ_t λ(t)ψ(tc) = λ(c)g_λ (`sum_lam_traceChar`), a quadratic twist;
* the middle cusps: Σ_{x≢0}Σ_t λ(t)χ(1 − s²)ψ(2tκ/(1 − s²)) = g_λλ(2κ)(J₆ − 1), J₆ = Σ_s(χλ)(1 − s²) a sextic Jacobi-type
  sum (`jacobi_double_sum_lam`), again a quadratic twist;
* the cusp 0: Σ_{x≢0}λ(x)χ(−9x²)ψ(−2κ/(9x)) = χ(−4)χ(9)⁻¹λ(−2)Σ_u(χλ)(u)ψ(uκ) (`gauss_low_sum_lam`): the **sextic**
  Gauss sum, so the cusp 0 reads the conjugate sextic twist;
* all main-term phases cancel (`sum_lam_middleMain`, `sum_lam_low`): the λ-weighted trace has no θ² main term.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The weighted decomposition -/

theorem fracTraceW_eq_sum (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (w : HyperbolicSpace) :
    P.fracTraceW φ Θ w = ∑ i : P.FracIndex, P.fracSumW φ Θ (complexMatrix (P.fracRep i) • w) := by
  have hF : ∀ δ ∈ P.levelSqGroup, ∀ x, P.fracSumW φ Θ (complexMatrix δ • x) = kubotaSquare δ * P.fracSumW φ Θ x :=
    fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact P.fracSumW_automorphy φ hφ Θ hΘ δ hδ x
  unfold fracTraceW cosetTrace
  rw [← P.fracCoset_bijective.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosetTerm_congr hF w (γ := (P.fracCoset i).out) (γ' := (P.fracRep i)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, P.complexCharacter_fracRep, inv_one, one_pow, one_mul]

section Points

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘ hΘr

/-- **The weighted fractional trace over the projective line modulo q².** -/
theorem fracTraceW_eq (φ : P.Res → ℂ) (hφ : P.SquareInvariant φ) (w : HyperbolicSpace) :
    P.fracTraceW φ Θ w = P.fracSumW φ Θ w +
      (∑ x : {x : P.Res // x ≠ 0}, P.fracSumW φ Θ (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) +
        ∑ s : P.Res × P.Res, P.fracSumW φ Θ (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • w)) := by
  rw [P.fracTraceW_eq_sum φ hφ Θ hΘ, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique]
  have h1 : P.fracSumW φ Θ (complexMatrix (P.fracRep (Sum.inl default)) • w) = P.fracSumW φ Θ w := by
    rw [show P.fracRep (Sum.inl default) = 1 from rfl, map_one, one_smul]
  have h2 : ∀ x : {x : P.Res // x ≠ 0}, P.fracSumW φ Θ (complexMatrix (P.fracRep (Sum.inr (Sum.inl x))) • w) =
      P.fracSumW φ Θ (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) := fun x => by
    rw [show P.fracRep (Sum.inr (Sum.inl x)) = lowerThree (P.p * P.lift x.1) from rfl]
  have h3 : ∀ s : P.Res × P.Res, P.fracSumW φ Θ (complexMatrix (P.fracRep (Sum.inr (Sum.inr s))) • w) =
      P.fracSumW φ Θ (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • w) := fun s => by
    rw [show P.fracRep (Sum.inr (Sum.inr s)) = P.gamma0 * transThree (P.sqLift s) from rfl, map_mul, mul_smul]
    unfold fracSumW
    exact Finset.sum_congr rfl fun t _ => by rw [P.fracCorrelation_S Θ hΘ hΘr P.sKM]
  rw [h1, Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_congr rfl (fun s _ => h3 s)]

/-- **The weighted sum at S.** -/
theorem fracSumW_sO (φ : P.Res → ℂ) (y : HyperbolicSpace) :
    P.fracSumW φ Θ (integralComplexMatrix sO • y) = φ 0 * Θ y ^ 2 +
      ∑ x : {x : P.Res // x ≠ 0}, φ x.1 * (P.chi (-9 * x.1 ^ 2) *
        (P.heckeLow Θ (-P.lowBeta (-P.lift x.1)) (P.contraction • y) *
          P.heckeLow Θ (-P.lowBeta (P.lift x.1)) (P.contraction • y))) := by
  have hS : ∀ x, Θ (integralComplexMatrix sO • x) = Θ x := hΘr ModularGroup.S
  unfold fracSumW
  rw [Fintype.sum_eq_add_sum_compl (0 : P.Res),
    Finset.sum_subtype _ (fun x => by simp : ∀ x, x ∈ ({0}ᶜ : Finset P.Res) ↔ x ≠ 0)]
  congr 1
  · rw [show P.lift 0 = P.lift (P.res 0) by rw [map_zero], P.fracCorrelation_lift Θ hΘ, fracCorrelation, neg_zero,
      P.fracShift_zero, one_smul, hS, pow_two]
  · refine Finset.sum_congr rfl fun x _ => ?_
    have hx : ¬ P.p ∣ P.lift x.1 := fun h => x.2 (P.res_lift_eq_zero h)
    have hx' : ¬ P.p ∣ -P.lift x.1 := fun h => hx (dvd_neg.mp h)
    rw [fracCorrelation, P.theta_fracShift_sO Θ hΘ hΘr _ hx, P.theta_fracShift_sO Θ hΘ hΘr _ hx', neg_neg,
      ← P.chi_res, ← P.chi_res, mul_mul_mul_comm, ← map_mul]
    congr 3
    simp only [map_mul, map_neg, res_lift, map_ofNat]
    ring

end Points

/-! ### The quadratic character of O/q -/

/-- The quadratic character λ_q of O/q, with complex values. -/
abbrev lam : MulChar P.Res ℂ := (quadraticChar P.Res).ringHomComp (Int.castRingHom ℂ)

theorem ringChar_ne_two (h2 : (2 : P.Res) ≠ 0) : ringChar P.Res ≠ 2 := by
  intro h
  apply h2
  have := ringChar.Nat.cast_ringChar (R := P.Res)
  rw [h] at this
  exact_mod_cast this

theorem lam_sq (x : P.Res) (hx : x ≠ 0) : P.lam x ^ 2 = 1 := by
  simp only [lam, MulChar.ringHomComp_apply]
  rw [← map_pow, quadraticChar_sq_one hx, map_one]

theorem lam_inv (x : P.Res) (hx : x ≠ 0) : (P.lam x)⁻¹ = P.lam x :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_two]; exact P.lam_sq x hx) |>.symm

theorem lam_squareInvariant : P.SquareInvariant (fun x => P.lam x) := by
  intro x d hd
  simp only [map_mul, map_pow, P.lam_sq d hd, mul_one]

theorem lam_ne_one (h2 : (2 : P.Res) ≠ 0) : P.lam ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (P.ringChar_ne_two h2)
  have hz : a ≠ 0 := by
    intro h0
    rw [h0, quadraticChar_zero] at ha
    norm_num at ha
  have := congrArg (fun χ : MulChar P.Res ℂ => χ a) h
  simp only [lam, MulChar.ringHomComp_apply, ha, MulChar.one_apply hz.isUnit] at this
  norm_num at this

theorem lam_sq_eq_one : P.lam ^ 2 = 1 := by
  ext u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply u.isUnit]
  exact P.lam_sq _ u.ne_zero

theorem chi_pow_mul_lam_ne_one (h2 : (2 : P.Res) ≠ 0) (k : ℕ) : P.chi ^ k * P.lam ≠ 1 := by
  intro h
  apply P.lam_ne_one h2
  have h3 : P.chi ^ 3 = 1 := primeCubicMulChar_cube P.p P.prime P.primary
  have hl : P.lam = (P.chi ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hl3 : P.lam ^ 3 = 1 := by rw [hl, inv_pow, ← pow_mul, mul_comm, pow_mul, h3, one_pow, inv_one]
  calc P.lam = P.lam ^ 3 * (P.lam ^ 2)⁻¹ := by group
    _ = 1 := by rw [hl3, P.lam_sq_eq_one, inv_one, mul_one]


/-! ### The λ-weighted character sums -/

theorem sum_lam_traceChar (h2 : (2 : P.Res) ≠ 0) (c : P.Res) :
    ∑ t : P.Res, P.lam t * P.traceChar (t * c) = P.lam c * gaussSum P.lam P.traceChar := by
  by_cases hc : c = 0
  · simp only [hc, mul_zero, AddChar.map_zero_eq_one, mul_one, MulChar.map_zero, zero_mul]
    exact MulChar.sum_eq_zero_of_ne_one (P.lam_ne_one h2)
  · have h := P.sum_mulChar_shift P.lam c 1 hc
    simp only [mul_one] at h
    rw [h, P.lam_inv c hc, gaussSum]

theorem sum_lam_eq_zero (h2 : (2 : P.Res) ≠ 0) : ∑ t : P.Res, P.lam t = 0 :=
  MulChar.sum_eq_zero_of_ne_one (P.lam_ne_one h2)

/-- The sextic Jacobi-type sum J₆ = Σ_s χ(1 − s²)λ(1 − s²). -/
def lamJacobi : ℂ := ∑ s : P.Res, P.chi (1 - s ^ 2) * P.lam (1 - s ^ 2)

/-- **The λ-weighted middle-cusp phases.** Σ_{x≢0}Σ_t λ(t)χ(1 − s²)ψ(2tκ/(1 − s²)) = g_λλ(2κ)(J₆ − 1), s = 9tx. -/
theorem jacobi_double_sum_lam (h2 : (2 : P.Res) ≠ 0) (κ : P.Res) :
    ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
        (P.chi (1 - (9 * t * x.1) ^ 2) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * κ)) =
      gaussSum P.lam P.traceChar * P.lam (2 * κ) * (P.lamJacobi - 1) := by
  have h9 := P.nine_ne_zero'
  set G := gaussSum P.lam P.traceChar with hG
  set f : P.Res → P.Res → ℂ := fun s t => P.chi (1 - s ^ 2) * P.traceChar (2 * t / (1 - s ^ 2) * κ) with hf
  have hstep4 : ∀ t : P.Res, P.lam t * ∑ x : P.Res, f (9 * t * x) t = P.lam t * ∑ s : P.Res, f s t := by
    intro t
    by_cases ht : t = 0
    · rw [ht, MulChar.map_zero, zero_mul, zero_mul]
    · exact congrArg (P.lam t * ·) ((mulLeft_bijective₀ (9 * t) (mul_ne_zero h9 ht)).sum_comp (fun s => f s t))
  have hstep3 : ∑ t : P.Res, P.lam t * f (9 * t * 0) t = P.lam (2 * κ) * G := by
    rw [hG, ← P.sum_lam_traceChar h2 (2 * κ)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hf, mul_zero, zero_pow two_ne_zero, sub_zero, MulChar.map_one, one_mul, div_one]
    congr 2
    ring
  have hstep56 : ∀ s : P.Res, ∑ t : P.Res, P.lam t * f s t =
      G * P.lam (2 * κ) * (P.chi (1 - s ^ 2) * P.lam (1 - s ^ 2)) := by
    intro s
    by_cases hs : 1 - s ^ 2 = 0
    · simp [hf, hs, MulChar.map_zero]
    · have e : ∀ t, P.lam t * f s t = P.chi (1 - s ^ 2) * (P.lam t * P.traceChar (t * (2 * κ * (1 - s ^ 2)⁻¹))) := by
        intro t
        simp only [hf]
        rw [show 2 * t / (1 - s ^ 2) * κ = t * (2 * κ * (1 - s ^ 2)⁻¹) by ring]
        ring
      rw [Finset.sum_congr rfl (fun t _ => e t), ← Finset.mul_sum, P.sum_lam_traceChar h2, map_mul,
        P.mulChar_inv_apply _ _ hs, P.lam_inv _ hs, hG]
      ring
  have hL : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
      (P.chi (1 - (9 * t * x.1) ^ 2) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * κ)) =
      ∑ x : {x : P.Res // x ≠ 0}, (fun x => ∑ t : P.Res, P.lam t * f (9 * t * x) t) x.1 := rfl
  rw [hL, P.sum_ne_zero_eq (fun x => ∑ t : P.Res, P.lam t * f (9 * t * x) t), hstep3]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hfull : ∑ t : P.Res, ∑ x : P.Res, P.lam t * f (9 * t * x) t = ∑ s : P.Res, G * P.lam (2 * κ) *
      (P.chi (1 - s ^ 2) * P.lam (1 - s ^ 2)) := by
    simp_rw [← Finset.mul_sum]
    simp_rw [hstep4]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => by rw [← hstep56 s]
  rw [hfull, ← Finset.mul_sum, lamJacobi]
  ring

/-- **The cusp-0 phases with the quadratic weight are a sextic Gauss sum.** -/
theorem gauss_low_sum_lam (h2 : (2 : P.Res) ≠ 0) (κ : P.Res) :
    ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) * P.traceChar (-2 * (9 * x.1)⁻¹ * κ)) =
      P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2) * ∑ u : P.Res, (P.chi u * P.lam u) * P.traceChar (u * κ) := by
  have h9 := P.nine_ne_zero'
  have hinvχ : ∀ a : P.Res, a ≠ 0 → P.chi a⁻¹ = (P.chi a)⁻¹ := fun a ha => P.mulChar_inv_apply P.chi a ha
  have hl9 : P.lam 9 = 1 := by
    rw [show (9 : P.Res) = 3 ^ 2 by norm_num, map_pow, P.lam_sq 3 P.three_ne_zero']
  set σ : P.Res → P.Res := fun x => -2 * (9 * x)⁻¹ with hσ
  have hinv : Function.Involutive σ := by
    intro x
    by_cases hx : x = 0
    · simp [hσ, hx]
    · simp only [hσ]
      field_simp
  have hfull : ∑ x : P.Res, P.lam x * (P.chi (-9 * x ^ 2) * P.traceChar (σ x * κ)) =
      P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2) * ∑ u : P.Res, (P.chi u * P.lam u) * P.traceChar (u * κ) := by
    rw [← hinv.bijective.sum_comp (fun x => P.lam x * (P.chi (-9 * x ^ 2) * P.traceChar (σ x * κ))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hinv u]
    by_cases hu : u = 0
    · simp [hσ, hu, MulChar.map_zero]
    · have e : -9 * σ u ^ 2 = (-4) * 9⁻¹ * u⁻¹ ^ 2 := by
        simp only [hσ]
        field_simp
        ring
      have el : P.lam (σ u) = P.lam (-2) * P.lam u := by
        simp only [hσ]
        rw [map_mul, P.mulChar_inv_apply _ _ (mul_ne_zero h9 hu), map_mul, hl9, one_mul, P.lam_inv _ hu]
      rw [e, el, map_mul, map_mul, map_pow, hinvχ 9 h9, hinvχ u hu, P.chi_inv_sq u hu]
      ring
  rw [P.sum_ne_zero_eq (fun x => P.lam x * (P.chi (-9 * x ^ 2) * P.traceChar (σ x * κ))), hfull]
  simp [MulChar.map_zero]

theorem chiSq_lam_sum (h2 : (2 : P.Res) ≠ 0) : ∑ x : P.Res, (P.chi ^ 2) x * P.lam x = 0 := by
  have := MulChar.sum_eq_zero_of_ne_one (P.chi_pow_mul_lam_ne_one h2 2)
  simpa [MulChar.mul_apply] using this

/-- The low–low phases with the quadratic weight cancel: Σ_{x≢0} λ(x)χ(−9x²) = 0. -/
theorem sum_lam_low (h2 : (2 : P.Res) ≠ 0) : ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * P.chi (-9 * x.1 ^ 2) = 0 := by
  rw [P.sum_ne_zero_eq (fun x => P.lam x * P.chi (-9 * x ^ 2))]
  have : ∑ x : P.Res, P.lam x * P.chi (-9 * x ^ 2) = P.chi (-9) * ∑ x : P.Res, (P.chi ^ 2) x * P.lam x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, map_pow, MulChar.pow_apply' _ (by norm_num)]
    ring
  rw [this, P.chiSq_lam_sum h2]
  simp [MulChar.map_zero]

/-- **The λ-weighted main phases of the middle cusps cancel.** -/
theorem sum_lam_middleMain (h2 : (2 : P.Res) ≠ 0) (A B : ℂ) :
    ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * P.middleMain x t A B = 0 := by
  have h9 := P.nine_ne_zero'
  have hsplit : ∀ x : {x : P.Res // x ≠ 0}, ∀ t : P.Res, P.middleMain x t A B =
      (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A else 0) +
        P.chi (1 - (9 * t * x.1) ^ 2) * B := by
    intro x t
    unfold middleMain
    by_cases h₁ : 1 + 9 * t * x.1 = 0
    · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 - 9 * t * x.1) * h₁
      rw [if_pos h₁, if_pos (Or.inl h₁), hsq, MulChar.map_zero, zero_mul, add_zero]
    · by_cases h₂ : 1 - 9 * t * x.1 = 0
      · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 + 9 * t * x.1) * h₂
        rw [if_neg h₁, if_pos h₂, if_pos (Or.inr h₂), hsq, MulChar.map_zero, zero_mul, add_zero]
      · rw [if_neg h₁, if_neg h₂, if_neg (not_or.mpr ⟨h₁, h₂⟩), zero_add]
  have hscale : ∀ (x : {x : P.Res // x ≠ 0}) (g : P.Res → ℂ),
      ∑ t : P.Res, P.lam t * g (9 * t * x.1) = P.lam (9 * x.1) * ∑ s : P.Res, P.lam s * g s := by
    intro x g
    have hx0 : (x.1 : P.Res) ≠ 0 := x.2
    have hx9 : 9 * x.1 ≠ 0 := mul_ne_zero h9 x.2
    rw [← (mulRight_bijective₀ (9 * x.1)⁻¹ (inv_ne_zero hx9)).sum_comp (fun t => P.lam t * g (9 * t * x.1)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show 9 * (s * (9 * x.1)⁻¹) * x.1 = s by field_simp, map_mul, P.mulChar_inv_apply _ _ hx9, P.lam_inv _ hx9]
    ring
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
  have hA : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
      (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A else 0) =
      P.chi 2 * A * (∑ s : P.Res, P.lam s * (if 1 + s = 0 ∨ 1 - s = 0 then (1 : ℂ) else 0)) *
        ((P.chi (3 * x.1))⁻¹ * P.lam (9 * x.1)) := by
    intro x
    have h := hscale x (fun s => if 1 + s = 0 ∨ 1 - s = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * A else 0)
    rw [h, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> ring
  have hB : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * (P.chi (1 - (9 * t * x.1) ^ 2) * B) =
      B * (∑ s : P.Res, P.lam s * P.chi (1 - s ^ 2)) * P.lam (9 * x.1) := by
    intro x
    rw [hscale x (fun s => P.chi (1 - s ^ 2) * B), Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  simp_rw [hA, hB]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
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
  have hz2 : ∑ x : {x : P.Res // x ≠ 0}, P.lam (9 * x.1) = 0 := by
    rw [P.sum_ne_zero_eq (fun x => P.lam (9 * x))]
    have : ∑ x : P.Res, P.lam (9 * x) = 0 := by
      rw [(mulLeft_bijective₀ (9 : P.Res) h9).sum_comp (fun x => P.lam x)]
      exact P.sum_lam_eq_zero h2
    rw [this]
    simp [MulChar.map_zero]
  rw [hz1, mul_zero, zero_add, hz2, mul_zero]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
