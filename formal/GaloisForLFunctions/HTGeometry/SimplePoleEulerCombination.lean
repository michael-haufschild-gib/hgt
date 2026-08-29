import GaloisForLFunctions.HTGeometry.TwistedDilationOrbitObstruction

/-!
# Euler combinations of a function with a simple pole

The Euler operator preserves regularity, and a nonzero constant-coefficient Euler combination of a
rational function with a simple pole at `1` has a pole at `1`: subtracting the principal part
leaves a regular function, and the principal part is a cotangent model up to a constant, where the
statement is already known.

This upgrades the cotangent-model obstruction of `DoubleSineOrbitResidueObstruction` to an
arbitrary simple pole, which is what a ramified `q`-difference equation produces.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

theorem RegularAt.mul {a b : RatFunc K} {c : K} (ha : RegularAt a c) (hb : RegularAt b c) :
    RegularAt (a * b) c := by
  obtain ⟨p₁, q₁, hq₁, rfl⟩ := ha
  obtain ⟨p₂, q₂, hq₂, rfl⟩ := hb
  refine ⟨p₁ * p₂, q₁ * q₂, by simp [hq₁, hq₂], ?_⟩
  rw [map_mul, map_mul, div_mul_div_comm]

theorem regularAt_toRF (p : Polynomial K) (c : K) : RegularAt (toRF p) c :=
  ⟨p, 1, by simp, by simp⟩

/-- The Euler operator preserves regularity. -/
theorem regularAt_ratFuncEulerOp {f : RatFunc K} {w : K} (hf : RegularAt f w) :
    RegularAt (ratFuncEulerOp f) w := by
  obtain ⟨p, q, hq, rfl⟩ := hf
  have hqne : toRF q ≠ 0 := RatFunc.algebraMap_ne_zero (fun h => hq (by simp [h]))
  have hfq : (toRF p / toRF q) * toRF q = toRF p := div_mul_cancel₀ _ hqne
  have hD := congrArg (ratFuncDerivative K) hfq
  rw [Derivation.leibniz, ratFuncDerivative_algebraMap, ratFuncDerivative_algebraMap] at hD
  simp only [smul_eq_mul] at hD
  have hval : ratFuncDerivative K (toRF p / toRF q)
      = (toRF (Polynomial.derivative p) * toRF q - toRF p * toRF (Polynomial.derivative q))
        / (toRF q * toRF q) := by
    rw [eq_div_iff (mul_ne_zero hqne hqne)]
    have hfe : toRF p / toRF q * toRF q = toRF p := hfq
    calc ratFuncDerivative K (toRF p / toRF q) * (toRF q * toRF q)
        = (ratFuncDerivative K (toRF p / toRF q) * toRF q) * toRF q := by ring
      _ = (toRF (Polynomial.derivative p)
            - (toRF p / toRF q) * toRF (Polynomial.derivative q)) * toRF q := by
          rw [show ratFuncDerivative K (toRF p / toRF q) * toRF q
              = toRF (Polynomial.derivative p)
                - toRF p / toRF q * toRF (Polynomial.derivative q) from by
            linear_combination hD]
      _ = toRF (Polynomial.derivative p) * toRF q
            - toRF p * toRF (Polynomial.derivative q) := by
          field_simp
  rw [ratFuncEulerOp, hval]
  refine RegularAt.mul (regularAt_toRF _ _) ?_
  refine ⟨Polynomial.derivative p * q - p * Polynomial.derivative q, q * q, by simp [hq], ?_⟩
  rw [map_sub, map_mul, map_mul, map_mul]

theorem regularAt_ratFuncEulerOp_iterate {f : RatFunc K} {w : K} (hf : RegularAt f w) (i : ℕ) :
    RegularAt (ratFuncEulerOp^[i] f) w := by
  induction i with
  | zero => simpa using hf
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact regularAt_ratFuncEulerOp ih

theorem regularAt_eulerCombination (a : ℕ → K) (r : ℕ) {f : RatFunc K} {w : K}
    (hf : RegularAt f w) : RegularAt (eulerCombination a r f) w := by
  rw [eulerCombination]
  refine regularAt_finsetSum _ _ fun i _ => ?_
  exact RegularAt.mul (regularAt_toRF _ _) (regularAt_ratFuncEulerOp_iterate hf i)

theorem ratFuncEulerOp_algebraMap (γ : K) : ratFuncEulerOp (algebraMap K (RatFunc K) γ) = 0 := by
  have h : algebraMap K (RatFunc K) γ
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C γ) := by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K), Polynomial.algebraMap_eq]
  rw [ratFuncEulerOp, h, ratFuncDerivative_algebraMap, Polynomial.derivative_C, map_zero, mul_zero]

theorem ratFuncEulerOp_iterate_zero (n : ℕ) : ratFuncEulerOp^[n] (0 : RatFunc K) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ratFuncEulerOp, map_zero, mul_zero]

theorem ratFuncEulerOp_iterate_add (n : ℕ) (w v : RatFunc K) :
    ratFuncEulerOp^[n] (w + v) = ratFuncEulerOp^[n] w + ratFuncEulerOp^[n] v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, ratFuncEulerOp, ratFuncEulerOp, ratFuncEulerOp,
        map_add, mul_add]

theorem eulerCombination_add (α : ℕ → K) (N : ℕ) (w v : RatFunc K) :
    eulerCombination α N (w + v) = eulerCombination α N w + eulerCombination α N v := by
  rw [eulerCombination, eulerCombination, eulerCombination, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add, ratFuncEulerOp_iterate_add]

theorem eulerCombination_algebraMap (α : ℕ → K) (N : ℕ) (γ : K) :
    eulerCombination α N (algebraMap K (RatFunc K) γ)
      = algebraMap K (RatFunc K) (α 0 * γ) := by
  rw [eulerCombination, Finset.sum_eq_single 0]
  · rw [Function.iterate_zero_apply, toRF, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K), ← map_mul]
  · intro i _ hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [Function.iterate_succ_apply, ratFuncEulerOp_algebraMap, ratFuncEulerOp_iterate_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

theorem cotModel_neg (c : K) : cotModel (-c) = -cotModel c := by
  rw [cotModel, cotModel, ← neg_div]
  congr 1
  rw [← map_neg]
  congr 1
  rw [map_neg, neg_mul]

theorem eulerCombination_neg (α : ℕ → K) (N : ℕ) (w : RatFunc K) :
    eulerCombination α N (-w) = -eulerCombination α N w := by
  have h := eulerCombination_add α N w (-w)
  rw [add_neg_cancel] at h
  have hz : eulerCombination α N (0 : RatFunc K) = 0 := by
    rw [eulerCombination]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ratFuncEulerOp_iterate_zero, mul_zero]
  rw [hz] at h
  linear_combination -h

/-! ## The principal part at a simple pole -/

theorem algebraMap_eq_toRF_C (x : K) : algebraMap K (RatFunc K) x = toRF (Polynomial.C x) := by
  rw [toRF, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- The cotangent model differs from a constant by a simple pole. -/
theorem cotModel_sub_const (c : K) :
    cotModel c - algebraMap K (RatFunc K) c
      = algebraMap K (RatFunc K) (2 * c) / toRF (linFac K) := by
  have hlin : toRF (linFac K) ≠ 0 := RatFunc.algebraMap_ne_zero linFac_ne_zero
  rw [cotModel, algebraMap_eq_toRF_C, algebraMap_eq_toRF_C, eq_div_iff hlin, sub_mul,
    div_mul_cancel₀ _ hlin, ← map_mul, ← map_sub]
  congr 1
  rw [linFac]
  simp only [map_mul, map_ofNat, Polynomial.C_1]
  ring

/-- **Principal part at a simple pole.**  A quotient whose denominator has a single factor `X - 1`
splits into its principal part at `1` and a function regular at `1`. -/
theorem exists_regularAt_sub_principalPart (A S : Polynomial K) (hS : S.eval 1 ≠ 0) :
    ∃ g : RatFunc K, RegularAt g 1 ∧
      toRF A / (toRF (linFac K) * toRF S)
        = algebraMap K (RatFunc K) (A.eval 1 / S.eval 1) / toRF (linFac K) + g := by
  have hSne : toRF S ≠ 0 := RatFunc.algebraMap_ne_zero (fun h => hS (by simp [h]))
  have hlin : toRF (linFac K) ≠ 0 := RatFunc.algebraMap_ne_zero linFac_ne_zero
  obtain ⟨ρ, hρ⟩ : ∃ ρ : K, ρ = A.eval 1 / S.eval 1 := ⟨_, rfl⟩
  have hroot : (A - Polynomial.C ρ * S).IsRoot 1 := by
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hρ]
    field_simp
    ring
  have hdvd : linFac K ∣ (A - Polynomial.C ρ * S) := by
    rw [linFac]
    exact Polynomial.dvd_iff_isRoot.mpr hroot
  obtain ⟨B, hB⟩ := hdvd
  refine ⟨toRF B / toRF S, ⟨B, S, hS, rfl⟩, ?_⟩
  have hAB : A = Polynomial.C ρ * S + linFac K * B := by
    rw [← hB]
    ring
  rw [← hρ, hAB,
    show toRF (Polynomial.C ρ * S + linFac K * B)
      = toRF (Polynomial.C ρ * S) + toRF (linFac K * B) from map_add _ _ _,
    show toRF (Polynomial.C ρ * S) = toRF (Polynomial.C ρ) * toRF S from map_mul _ _ _,
    show toRF (linFac K * B) = toRF (linFac K) * toRF B from map_mul _ _ _,
    algebraMap_eq_toRF_C, div_add_div _ _ hlin hSne, mul_comm (toRF (linFac K)) (toRF B)]

set_option maxHeartbeats 1000000 in
/-- **A nonzero constant-coefficient Euler combination of a function with a simple pole at `1`
has a pole at `1`.** -/
theorem not_regularAt_one_eulerCombination_simplePole [CharZero K] (A S : Polynomial K)
    (hS : S.eval 1 ≠ 0) (hA : A.eval 1 ≠ 0) (a : ℕ → K) (r : ℕ) (har : a r ≠ 0) :
    ¬ RegularAt (eulerCombination a r (toRF A / (toRF (linFac K) * toRF S))) 1 := by
  obtain ⟨g, hgreg, hsplit⟩ := exists_regularAt_sub_principalPart A S hS
  set ρ : K := A.eval 1 / S.eval 1 with hρ
  have hρne : ρ ≠ 0 := div_ne_zero hA hS
  have hprinc : algebraMap K (RatFunc K) ρ / toRF (linFac K)
      = cotModel (ρ / 2) - algebraMap K (RatFunc K) (ρ / 2) := by
    rw [cotModel_sub_const]
    congr 2
    ring
  rw [hsplit, hprinc]
  have hlin : eulerCombination a r (cotModel (ρ / 2) - algebraMap K (RatFunc K) (ρ / 2) + g)
      = eulerCombination a r (cotModel (ρ / 2))
        + (-algebraMap K (RatFunc K) (a 0 * (ρ / 2)) + eulerCombination a r g) := by
    rw [show cotModel (ρ / 2) - algebraMap K (RatFunc K) (ρ / 2) + g
        = cotModel (ρ / 2) + (-algebraMap K (RatFunc K) (ρ / 2) + g) from by ring,
      eulerCombination_add, eulerCombination_add, eulerCombination_neg,
      eulerCombination_algebraMap]
  rw [hlin]
  refine not_regularAt_add_left
    (not_regularAt_one_eulerCombination_cotModel a (ρ / 2) (by simpa using hρne) r har) ?_
  exact RegularAt.add (regularAt_algebraMap _ _).neg (regularAt_eulerCombination a r hgreg)

/-! ## An arbitrary simple pole -/

theorem polyScale_linFac_shift (p₀ : K) :
    polyScale p₀ (Polynomial.X - Polynomial.C p₀) = Polynomial.C p₀ * linFac K := by
  rw [polyScale_eq_comp, linFac]
  simp [Polynomial.sub_comp, Polynomial.mul_comp]
  ring

set_option maxHeartbeats 1000000 in
/-- **A nonzero Euler combination of a function with a simple pole at `p₀ ≠ 0` has a pole
there.**  Dilating the coordinate moves the pole to `1`, and the Euler operator commutes with
dilation. -/
theorem not_regularAt_eulerCombination_simplePole [CharZero K] (p₀ : K) (hp₀ : p₀ ≠ 0)
    (A S : Polynomial K) (hS : S.eval p₀ ≠ 0) (hA : A.eval p₀ ≠ 0)
    (a : ℕ → K) (r : ℕ) (har : a r ≠ 0) :
    ¬ RegularAt (eulerCombination a r
      (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S))) p₀ := by
  intro hreg
  have hscale : RegularAt (ratFuncScale p₀ hp₀ (eulerCombination a r
      (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)))) 1 := by
    rw [regularAt_ratFuncScale, mul_one]
    exact hreg
  rw [← eulerCombination_ratFuncScale] at hscale
  have hsplit : ratFuncScale p₀ hp₀
      (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S))
      = toRF (polyScale p₀ A)
        / (toRF (linFac K) * toRF (Polynomial.C p₀ * polyScale p₀ S)) := by
    have h1 : toRF (Polynomial.X - Polynomial.C p₀) * toRF S
        = toRF ((Polynomial.X - Polynomial.C p₀) * S) := (map_mul _ _ _).symm
    have h2 : polyScale p₀ ((Polynomial.X - Polynomial.C p₀) * S)
        = linFac K * (Polynomial.C p₀ * polyScale p₀ S) := by
      rw [map_mul, polyScale_linFac_shift]
      ring
    have h3 : algebraMap (Polynomial K) (RatFunc K)
          (linFac K * (Polynomial.C p₀ * polyScale p₀ S))
        = toRF (linFac K) * toRF (Polynomial.C p₀ * polyScale p₀ S) := map_mul _ _ _
    rw [h1, ratFuncScale_div, h2, h3]
  rw [hsplit] at hscale
  refine not_regularAt_one_eulerCombination_simplePole (polyScale p₀ A)
    (Polynomial.C p₀ * polyScale p₀ S) ?_ ?_ a r har hscale
  · rw [Polynomial.eval_mul, Polynomial.eval_C, eval_polyScale, mul_one]
    exact mul_ne_zero hp₀ hS
  · rw [eval_polyScale, mul_one]
    exact hA

/-- **The twisted orbit obstruction for a simple-pole Euler combination.**  A nonzero Euler
combination of a function with a simple pole at `p₀` and no other pole on the orbit `p₀ q^ℤ` is not
a twisted dilation coboundary. -/
theorem not_twistedDilationTelescoped_simplePole [CharZero K] (q γ p₀ : K) (hq : q ≠ 0)
    (hγ : γ ≠ 0) (hp₀ : p₀ ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (A S : Polynomial K) (hS : S.eval p₀ ≠ 0) (hA : A.eval p₀ ≠ 0)
    (hreg : ∀ n : ℤ, n ≠ 0 →
      RegularAt (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)) (p₀ * q ^ n))
    (a : ℕ → K) (r : ℕ) (har : a r ≠ 0) :
    ¬ ∃ y : RatFunc K,
      eulerCombination a r (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S))
        = algebraMap K (RatFunc K) γ * ratFuncScale q hq y - y := by
  refine not_twistedDilationTelescoped_of_unique_multOrbit_pole q p₀ γ hq hp₀ hγ hqtor _ ?_ ?_
  · exact not_regularAt_eulerCombination_simplePole p₀ hp₀ A S hS hA a r har
  · intro n hn
    exact regularAt_eulerCombination a r (hreg n hn)

/-- Regularity of a simple-pole quotient away from its poles. -/
theorem regularAt_simplePoleQuotient (A S : Polynomial K) (p₀ w : K)
    (hden : (Polynomial.X - Polynomial.C p₀).eval w ≠ 0) (hS : S.eval w ≠ 0) :
    RegularAt (toRF A / (toRF (Polynomial.X - Polynomial.C p₀) * toRF S)) w :=
  ⟨A, (Polynomial.X - Polynomial.C p₀) * S, by
    rw [Polynomial.eval_mul]
    exact mul_ne_zero hden hS, by rw [map_mul]⟩


end

end GaloisForLFunctions.HTGeometry
