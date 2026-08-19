import GaloisForLFunctions.RHTower.PrimeCoShiftModel
import GaloisForLFunctions.HTGeometry.AdjointTransverseLowerBound

/-!
# The kernel projection of a one-prime co-shift resolvent

For a positive integer `p` and a scalar `a` with `|a| < 1`, the operator

```
T = V_p^* - a
```

has a closed kernel whose orthogonal projection is given by the closed formula

```
P = (1 - |a|²) B E B^*,   B = (1 - a V_p)^{-1},   E = 1 - V_p V_p^*.
```

Everything is proved inside the C*-algebra `H →L[ℂ] H` from four relations: `V_p^* V_p = 1`,
`V_p^* E = 0`, `E V_p = 0`, `E² = E`, together with the Neumann unit `B`.  The resulting formula is
manifestly a *word in the isometries*, so for two distinct primes the two projections commute as
soon as the underlying isometries doubly commute — which is exactly what unique factorization
gives.

The formula is also what produces the one-prime reduced minimum modulus: `T`'s adjoint
`V_p - conj a` is bounded below by `1 - |a|`, so `T` is bounded below by `1 - |a|` on the orthogonal
complement of its kernel.
-/

open scoped ENNReal NNReal InnerProductSpace
open RHTower

namespace RHTower.PrimeCoShift

noncomputable section


/-- `V_p` as a bounded operator. -/
def Vop (p : ℕ+) : H →L[ℂ] H := (primeShift p).toContinuousLinearMap

theorem star_Vop (p : ℕ+) : star (Vop p) = primeCoShift p := by
  rw [ContinuousLinearMap.star_eq_adjoint, Vop, ← primeCoShift_eq_adjoint]

theorem star_primeCoShift (p : ℕ+) : star (primeCoShift p) = Vop p := by
  rw [← star_Vop p, star_star]

theorem Vop_apply_mul (p : ℕ+) (y : H) (n : ℕ+) : Vop p y (p * n) = y n :=
  lpScalarInjection_coordinate (fun n : ℕ+ => p * n) (mulLeft_injective p) y n

theorem Vop_apply_of_not_dvd (p : ℕ+) (y : H) (m : ℕ+) (h : ¬ ((p : ℕ) ∣ (m : ℕ))) :
    Vop p y m = 0 := by
  classical
  have hcoord : Vop p y m = ⟪lp.single 2 m (1 : ℂ), Vop p y⟫_ℂ := by
    rw [lp.inner_single_left]
    simp
  have hadj : Vop p = ContinuousLinearMap.adjoint (primeCoShift p) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_primeCoShift]
  have hzero : primeCoShift p (lp.single 2 m (1 : ℂ)) = 0 := by
    apply lp.ext
    funext i
    rw [primeCoShift_apply, lp.single_apply]
    have hne : p * i ≠ m := by
      intro hEq
      exact h ⟨(i : ℕ), by simpa using congrArg (fun z : ℕ+ => (z : ℕ)) hEq.symm⟩
    simp [hne]
  rw [hcoord, hadj, ContinuousLinearMap.adjoint_inner_right, hzero]
  simp

theorem coShift_mul_Vop (p : ℕ+) : primeCoShift p * Vop p = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [ContinuousLinearMap.mul_apply, primeCoShift_apply, Vop_apply_mul]
  rfl

/-- `E_p = 1 - V_p V_p^*`, the projection onto `ker V_p^*`. -/
def Eop (p : ℕ+) : H →L[ℂ] H := 1 - Vop p * primeCoShift p

theorem star_Eop (p : ℕ+) : star (Eop p) = Eop p := by
  rw [Eop, star_sub, star_one, star_mul, star_primeCoShift, star_Vop]

theorem coShift_mul_Eop (p : ℕ+) : primeCoShift p * Eop p = 0 := by
  rw [Eop, mul_sub, mul_one, ← mul_assoc, coShift_mul_Vop, one_mul, sub_self]

theorem Eop_mul_Vop (p : ℕ+) : Eop p * Vop p = 0 := by
  rw [Eop, sub_mul, one_mul, mul_assoc, coShift_mul_Vop, mul_one, sub_self]

theorem Eop_mul_Eop (p : ℕ+) : Eop p * Eop p = Eop p := by
  rw [Eop]
  rw [sub_mul, one_mul, mul_sub, mul_one, mul_assoc (Vop p), ← mul_assoc (primeCoShift p),
    coShift_mul_Vop, one_mul]
  abel

theorem coShift_commute (p q : ℕ+) : Commute (primeCoShift p) (primeCoShift q) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    primeCoShift_apply, primeCoShift_apply, primeCoShift_apply, primeCoShift_apply]
  rw [mul_left_comm q p n]

theorem Vop_commute (p q : ℕ+) : Commute (Vop p) (Vop q) := by
  have h := coShift_commute q p
  have := congrArg star h
  rwa [star_mul, star_mul, star_primeCoShift, star_primeCoShift] at this

theorem coShift_commute_Vop {p q : ℕ+} (hcop : Nat.Coprime (q : ℕ) (p : ℕ)) :
    Commute (primeCoShift p) (Vop q) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, primeCoShift_apply]
  by_cases hd : (q : ℕ) ∣ (n : ℕ)
  · obtain ⟨c, hc⟩ := hd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exfalso; rw [h0, Nat.mul_zero] at hc; exact absurd hc (n.property).ne'
      · exact h0
    set m : ℕ+ := ⟨c, hcpos⟩ with hm
    have hn : n = q * m := PNat.coe_injective (by simpa [hm] using hc)
    subst hn
    rw [show p * (q * m) = q * (p * m) from mul_left_comm p q m]
    rw [Vop_apply_mul, Vop_apply_mul, primeCoShift_apply]
  · have hd2 : ¬ ((q : ℕ) ∣ ((p : ℕ) * (n : ℕ))) := by
      intro hdd
      exact hd (hcop.dvd_of_dvd_mul_left hdd)
    rw [Vop_apply_of_not_dvd _ _ _ hd, Vop_apply_of_not_dvd _ _ _ (by simpa using hd2)]

/-! ### The Neumann unit `B = (1 - a V_p)^{-1}` -/

section Neumann

variable {a : ℂ}

theorem norm_smul_Vop_lt (p : ℕ+) (ha : ‖a‖ < 1) : ‖a • Vop p‖ < 1 := by
  rw [norm_smul]
  have h1 : ‖Vop p‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  calc ‖a‖ * ‖Vop p‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
    _ = ‖a‖ := mul_one _
    _ < 1 := ha

/-- The Neumann unit `1 - a V_p`. -/
def Bunit (p : ℕ+) (ha : ‖a‖ < 1) : (H →L[ℂ] H)ˣ :=
  Units.oneSub (a • Vop p) (norm_smul_Vop_lt p ha)

theorem Bunit_val (p : ℕ+) (ha : ‖a‖ < 1) :
    ((Bunit p ha : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = 1 - a • Vop p :=
  Units.val_oneSub _ _

/-- The one-prime resolvent `B = (1 - a V_p)^{-1}`. -/
def Bop (p : ℕ+) (ha : ‖a‖ < 1) : H →L[ℂ] H := ↑(Bunit p ha)⁻¹

theorem Bop_mul_left (p : ℕ+) (ha : ‖a‖ < 1) : (1 - a • Vop p) * Bop p ha = 1 := by
  rw [Bop, ← Bunit_val p ha]
  exact (Bunit p ha).mul_inv

theorem Bop_mul_right (p : ℕ+) (ha : ‖a‖ < 1) : Bop p ha * (1 - a • Vop p) = 1 := by
  rw [Bop, ← Bunit_val p ha]
  exact (Bunit p ha).inv_mul

theorem Bop_eq_one_add_left (p : ℕ+) (ha : ‖a‖ < 1) :
    Bop p ha = 1 + a • (Vop p * Bop p ha) := by
  have h := Bop_mul_left p ha
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  exact sub_eq_iff_eq_add.mp h

theorem Bop_eq_one_add_right (p : ℕ+) (ha : ‖a‖ < 1) :
    Bop p ha = 1 + a • (Bop p ha * Vop p) := by
  have h := Bop_mul_right p ha
  rw [mul_sub, mul_one, mul_smul_comm] at h
  exact sub_eq_iff_eq_add.mp h

theorem coShift_mul_Bop (p : ℕ+) (ha : ‖a‖ < 1) :
    primeCoShift p * Bop p ha = primeCoShift p + a • Bop p ha := by
  conv_lhs => rw [Bop_eq_one_add_left p ha]
  rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc, coShift_mul_Vop, one_mul]

theorem star_Bop_mul_right (p : ℕ+) (ha : ‖a‖ < 1) :
    star (Bop p ha) * (1 - star a • primeCoShift p) = 1 := by
  have h := congrArg star (Bop_mul_left p ha)
  rw [star_mul, star_sub, star_one, star_smul, star_Vop] at h
  exact h

theorem star_Bop_mul_left (p : ℕ+) (ha : ‖a‖ < 1) :
    (1 - star a • primeCoShift p) * star (Bop p ha) = 1 := by
  have h := congrArg star (Bop_mul_right p ha)
  rw [star_mul, star_sub, star_one, star_smul, star_Vop] at h
  exact h

theorem star_Bop_eq (p : ℕ+) (ha : ‖a‖ < 1) :
    star (Bop p ha) = 1 + star a • (star (Bop p ha) * primeCoShift p) := by
  have h := star_Bop_mul_right p ha
  rw [mul_sub, mul_one, mul_smul_comm] at h
  exact sub_eq_iff_eq_add.mp h

end Neumann

/-! ### The closed-form kernel projection -/

section Projection

variable {a : ℂ}

/-- `γ = 1 - |a|²`. -/
def gammaC (a : ℂ) : ℂ := 1 - star a * a

theorem gammaC_eq (a : ℂ) : gammaC a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
  have hmul : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star a = (starRingEnd ℂ) a from rfl, mul_comm, Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq]
  rw [gammaC, hmul]
  push_cast
  ring

theorem gammaC_ne_zero (ha : ‖a‖ < 1) : gammaC a ≠ 0 := by
  rw [gammaC_eq]
  have h : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  exact_mod_cast h.ne'

theorem star_gammaC (a : ℂ) : star (gammaC a) = gammaC a := by
  rw [gammaC_eq]
  simp

theorem gamma_smul_starBop_Bop (p : ℕ+) (ha : ‖a‖ < 1) :
    gammaC a • (star (Bop p ha) * Bop p ha)
      = Bop p ha + star a • (star (Bop p ha) * primeCoShift p) := by
  have h1 : star (Bop p ha) = 1 + star a • (star (Bop p ha) * primeCoShift p) :=
    star_Bop_eq p ha
  have key : star (Bop p ha) * Bop p ha
      = Bop p ha + star a • (star (Bop p ha) * primeCoShift p)
        + (star a * a) • (star (Bop p ha) * Bop p ha) := by
    conv_lhs => rw [h1]
    rw [add_mul, one_mul, smul_mul_assoc, mul_assoc, coShift_mul_Bop, mul_add, mul_smul_comm,
      smul_add, mul_smul]
    exact (add_assoc _ _ _).symm
  rw [gammaC, sub_smul, one_smul]
  nth_rewrite 1 [key]
  abel

theorem Eop_mul_Bop_mul_Eop (p : ℕ+) (ha : ‖a‖ < 1) :
    Eop p * Bop p ha * Eop p = Eop p := by
  conv_lhs => rw [Bop_eq_one_add_left p ha]
  rw [mul_add, mul_one, mul_smul_comm, add_mul, smul_mul_assoc, ← mul_assoc (Eop p) (Vop p),
    Eop_mul_Vop, zero_mul, zero_mul, smul_zero, add_zero, Eop_mul_Eop]

theorem Eop_mul_starBop_coShift_mul_Eop (p : ℕ+) (ha : ‖a‖ < 1) :
    Eop p * (star (Bop p ha) * primeCoShift p) * Eop p = 0 := by
  rw [mul_assoc (Eop p), mul_assoc, coShift_mul_Eop, mul_zero, mul_zero]

/-- **The compressed resolvent norm.**  `E B^* B E = γ^{-1} E`. -/
theorem Eop_starBop_Bop_Eop (p : ℕ+) (ha : ‖a‖ < 1) :
    Eop p * star (Bop p ha) * Bop p ha * Eop p = (gammaC a)⁻¹ • Eop p := by
  have hmul : gammaC a • (Eop p * (star (Bop p ha) * Bop p ha) * Eop p) = Eop p := by
    calc gammaC a • (Eop p * (star (Bop p ha) * Bop p ha) * Eop p)
        = Eop p * (gammaC a • (star (Bop p ha) * Bop p ha)) * Eop p := by
          rw [mul_smul_comm, smul_mul_assoc]
      _ = Eop p * (Bop p ha + star a • (star (Bop p ha) * primeCoShift p)) * Eop p := by
          rw [gamma_smul_starBop_Bop]
      _ = Eop p * Bop p ha * Eop p
            + star a • (Eop p * (star (Bop p ha) * primeCoShift p) * Eop p) := by
          rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
      _ = Eop p := by
          rw [Eop_mul_Bop_mul_Eop, Eop_mul_starBop_coShift_mul_Eop, smul_zero, add_zero]
  have hassoc : Eop p * star (Bop p ha) * Bop p ha * Eop p
      = Eop p * (star (Bop p ha) * Bop p ha) * Eop p := by
    rw [mul_assoc (Eop p)]
  have h2 := congrArg (fun T : H →L[ℂ] H => (gammaC a)⁻¹ • T) hmul
  simp only [smul_smul, inv_mul_cancel₀ (gammaC_ne_zero ha), one_smul] at h2
  rw [hassoc, h2]

/-- The closed-form orthogonal projection onto `ker (V_p^* - a)`. -/
def Pop (p : ℕ+) (ha : ‖a‖ < 1) : H →L[ℂ] H :=
  gammaC a • (Bop p ha * Eop p * star (Bop p ha))

theorem star_Pop (p : ℕ+) (ha : ‖a‖ < 1) : star (Pop p ha) = Pop p ha := by
  rw [Pop, star_smul, star_gammaC]
  congr 1
  rw [star_mul, star_mul, star_star, star_Eop, mul_assoc]

theorem Pop_mul_Pop (p : ℕ+) (ha : ‖a‖ < 1) : Pop p ha * Pop p ha = Pop p ha := by
  rw [Pop]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hmid : Bop p ha * Eop p * star (Bop p ha) * (Bop p ha * Eop p * star (Bop p ha))
      = Bop p ha * (Eop p * star (Bop p ha) * Bop p ha * Eop p) * star (Bop p ha) := by
    simp only [mul_assoc]
  rw [hmid, Eop_starBop_Bop_Eop, mul_smul_comm, smul_mul_assoc, smul_smul]
  congr 1
  field_simp

/-- `T = V_p^* - a`. -/
def Top (p : ℕ+) (a : ℂ) : H →L[ℂ] H := primeCoShift p - a • (1 : H →L[ℂ] H)

@[simp] theorem Top_apply (p : ℕ+) (a : ℂ) (x : H) : Top p a x = primeCoShift p x - a • x := by
  simp [Top]

theorem Top_mul_Bop (p : ℕ+) (ha : ‖a‖ < 1) : Top p a * Bop p ha = primeCoShift p := by
  rw [Top, sub_mul, smul_mul_assoc, one_mul, coShift_mul_Bop]
  abel

theorem Top_mul_Pop (p : ℕ+) (ha : ‖a‖ < 1) : Top p a * Pop p ha = 0 := by
  rw [Pop, mul_smul_comm]
  have h : Top p a * (Bop p ha * Eop p * star (Bop p ha)) = 0 := by
    rw [show Bop p ha * Eop p * star (Bop p ha) = Bop p ha * (Eop p * star (Bop p ha)) by
      rw [mul_assoc], ← mul_assoc, Top_mul_Bop, ← mul_assoc, coShift_mul_Eop, zero_mul]
  rw [h, smul_zero]

theorem Pop_apply_of_mem_ker (p : ℕ+) (ha : ‖a‖ < 1) {x : H} (hx : Top p a x = 0) :
    Pop p ha x = x := by
  have hV : primeCoShift p x = a • x := by
    have h := Top_apply p a x
    rw [hx] at h
    exact sub_eq_zero.mp h.symm
  have hstar : gammaC a • (star (Bop p ha) x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) (star_Bop_mul_right p ha)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, hV, smul_smul] at h
    have hx' : x - (star a * a) • x = gammaC a • x := by
      rw [gammaC, sub_smul, one_smul]
    rw [hx', map_smul] at h
    exact h
  have hstar' : star (Bop p ha) x = (gammaC a)⁻¹ • x := by
    have h2 := congrArg (fun z : H => (gammaC a)⁻¹ • z) hstar
    simpa [smul_smul, inv_mul_cancel₀ (gammaC_ne_zero ha)] using h2
  have hEx : Eop p x = x - a • (Vop p x) := by
    simp [Eop, hV]
  have hBEx : Bop p ha (Eop p x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) (Bop_eq_one_add_right p ha)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] at h
    rw [hEx, map_sub, map_smul]
    rw [h]
    abel
  have hPop : Pop p ha x = gammaC a • (Bop p ha (Eop p (star (Bop p ha) x))) := rfl
  rw [hPop, hstar', map_smul, map_smul, hBEx, smul_smul,
    mul_inv_cancel₀ (gammaC_ne_zero ha), one_smul]

end Projection

/-! ### `Pop` is the orthogonal projection onto `ker T` -/

section StarProjection

variable {a : ℂ}

theorem starProjection_ker_Top (p : ℕ+) (ha : ‖a‖ < 1) (x : H) :
    (LinearMap.ker (Top p a : H →ₗ[ℂ] H)).starProjection x = Pop p ha x := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · show Top p a (Pop p ha x) = 0
    have h := congrArg (fun T : H →L[ℂ] H => T x) (Top_mul_Pop p ha)
    simpa using h
  · intro w hw
    have hw' : Top p a w = 0 := hw
    have hPw : Pop p ha w = w := Pop_apply_of_mem_ker p ha hw'
    have hsa : ContinuousLinearMap.adjoint (Pop p ha) = Pop p ha := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_Pop]
    have hadj := ContinuousLinearMap.adjoint_inner_left (Pop p ha) w x
    rw [hsa] at hadj
    rw [inner_sub_left, hadj, hPw, sub_self]

theorem adjoint_Top (p : ℕ+) (a : ℂ) :
    ContinuousLinearMap.adjoint (Top p a) = Vop p - star a • (1 : H →L[ℂ] H) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, Top, star_sub, star_smul, star_one,
    star_primeCoShift]

theorem norm_adjoint_Top_ge (p : ℕ+) (a : ℂ) (y : H) :
    (1 - ‖a‖) * ‖y‖ ≤ ‖ContinuousLinearMap.adjoint (Top p a) y‖ := by
  rw [adjoint_Top]
  have hval : (Vop p - star a • (1 : H →L[ℂ] H)) y = Vop p y - star a • y := by
    simp
  rw [hval]
  have hiso : ‖Vop p y‖ = ‖y‖ := (primeShift p).norm_map y
  have hsmul : ‖star a • y‖ = ‖a‖ * ‖y‖ := by
    rw [norm_smul]
    simp
  calc (1 - ‖a‖) * ‖y‖ = ‖Vop p y‖ - ‖star a • y‖ := by rw [hiso, hsmul]; ring
    _ ≤ ‖Vop p y - star a • y‖ := norm_sub_norm_le _ _

/-- **The one-prime reduced minimum modulus.** -/
theorem norm_Top_ge_of_mem_orthogonal (p : ℕ+) (ha : ‖a‖ < 1)
    {x : H} (hx : x ∈ (LinearMap.ker (Top p a : H →ₗ[ℂ] H))ᗮ) :
    (1 - ‖a‖) * ‖x‖ ≤ ‖Top p a x‖ :=
  GaloisForLFunctions.HTGeometry.transverse_lower_bound_of_adjoint_bounded_below
    (Top p a) (by linarith) (norm_adjoint_Top_ge p a) x hx

/-- **The one-prime gap.**  `‖T x‖ ≥ (1-|a|)‖x - P x‖` for the kernel projection `P`. -/
theorem norm_Top_ge_norm_sub_Pop (p : ℕ+) (ha : ‖a‖ < 1) (x : H) :
    (1 - ‖a‖) * ‖x - Pop p ha x‖ ≤ ‖Top p a x‖ := by
  set K := LinearMap.ker (Top p a : H →ₗ[ℂ] H) with hK
  have hmem : x - Pop p ha x ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    rw [← starProjection_ker_Top p ha x]
    exact K.starProjection_inner_eq_zero x w hw
  have hTeq : Top p a (x - Pop p ha x) = Top p a x := by
    rw [map_sub]
    have h := congrArg (fun T : H →L[ℂ] H => T x) (Top_mul_Pop p ha)
    have h0 : Top p a (Pop p ha x) = 0 := by simpa using h
    rw [h0, sub_zero]
  have := norm_Top_ge_of_mem_orthogonal p ha hmem
  rwa [hTeq] at this

end StarProjection

/-! ### Commutation of the kernel projections at distinct primes -/

section Commutation

variable {a b : ℂ}

theorem commute_smul_right {X Y : H →L[ℂ] H} (h : Commute X Y) (c : ℂ) :
    Commute X (c • Y) := by
  show X * (c • Y) = (c • Y) * X
  rw [mul_smul_comm, smul_mul_assoc, h.eq]

theorem commute_smul_left {X Y : H →L[ℂ] H} (h : Commute X Y) (c : ℂ) :
    Commute (c • X) Y := (commute_smul_right h.symm c).symm

theorem commute_Bop_right {X : H →L[ℂ] H} (q : ℕ+) (hb : ‖b‖ < 1)
    (h : Commute X (Vop q)) : Commute X (Bop q hb) := by
  have h1 : Commute X ((Bunit q hb : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) := by
    rw [Bunit_val]
    exact (Commute.one_right X).sub_right (commute_smul_right h b)
  exact h1.units_inv_right

theorem commute_star_Bop_right {X : H →L[ℂ] H} (q : ℕ+) (hb : ‖b‖ < 1)
    (h : Commute (star X) (Vop q)) : Commute X (star (Bop q hb)) := by
  have h1 : Commute (star X) (Bop q hb) := commute_Bop_right q hb h
  have h2 := commute_star_star.mpr h1
  rwa [star_star] at h2

theorem commute_Eop_right {X : H →L[ℂ] H} (q : ℕ+)
    (hV : Commute X (Vop q)) (hC : Commute X (primeCoShift q)) : Commute X (Eop q) := by
  rw [Eop]
  exact (Commute.one_right X).sub_right (hV.mul_right hC)

theorem commute_Pop_right {X : H →L[ℂ] H} (q : ℕ+) (hb : ‖b‖ < 1)
    (hV : Commute X (Vop q)) (hC : Commute X (primeCoShift q))
    (hVs : Commute (star X) (Vop q)) : Commute X (Pop q hb) := by
  rw [Pop]
  refine commute_smul_right ?_ _
  exact ((commute_Bop_right q hb hV).mul_right (commute_Eop_right q hV hC)).mul_right
    (commute_star_Bop_right q hb hVs)

/-- **Doubly commuting isometries give commuting kernel projections.** -/
theorem commute_Pop_Pop {p q : ℕ+} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hpq : Nat.Coprime (p : ℕ) (q : ℕ)) :
    Commute (Pop p ha) (Pop q hb) := by
  have hqp : Nat.Coprime (q : ℕ) (p : ℕ) := hpq.symm
  have hVV : Commute (Vop p) (Vop q) := Vop_commute p q
  have hCV : Commute (primeCoShift p) (Vop q) := coShift_commute_Vop hqp
  have hVC : Commute (Vop p) (primeCoShift q) := (coShift_commute_Vop hpq).symm
  have hCC : Commute (primeCoShift p) (primeCoShift q) := coShift_commute p q
  -- the generators of the `p`-word commute with `P_q`
  have hVP : Commute (Vop p) (Pop q hb) := by
    refine commute_Pop_right q hb hVV hVC ?_
    rw [star_Vop]
    exact hCV
  have hCP : Commute (primeCoShift p) (Pop q hb) := by
    refine commute_Pop_right q hb hCV hCC ?_
    rw [star_primeCoShift]
    exact hVV
  have hBP : Commute (Bop p ha) (Pop q hb) :=
    (commute_Bop_right p ha hVP.symm).symm
  have hsBP : Commute (star (Bop p ha)) (Pop q hb) := by
    have h2 := commute_star_star.mpr hBP
    rwa [star_Pop] at h2
  have hEP : Commute (Eop p) (Pop q hb) :=
    (commute_Eop_right p hVP.symm hCP.symm).symm
  rw [Pop]
  exact commute_smul_left ((hBP.mul_left hEP).mul_left hsBP) _

end Commutation

end

end RHTower.PrimeCoShift
