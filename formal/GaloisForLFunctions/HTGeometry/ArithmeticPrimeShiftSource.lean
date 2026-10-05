import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.HTGeometry.LpInjectionCompression

/-!
# The arithmetic prime-shift source

On `H = ℓ²(ℕ≥1)` with coordinate vectors `e_n`:

* the logarithmic generator `L e_n = (log n) e_n` on the finite-support core `(APS.1)` and its
  bounded heat semigroup `S_t e_n = n^{-t} e_n`, `t ≥ 0` `(APS.2)`;
* the multiplicative isometries `V_m e_n = e_{mn}` with `V_m V_n = V_{mn}` `(APS.3)`;
* the source commutator `[L, V_m] = (log m) V_m` on the core `(APS.4)`, which extends to the
  bounded letter `A_m = (log m) V_m` `(APS.5)`;
* the intertwining `S_t V_m = m^{-t} V_m S_t` `(APS.7)`, which collapses the Duhamel responses
  `D_m(t) = -∫₀ᵗ S_{t-s} V_m S_s ds` and `D̃_m(t) = -∫₀ᵗ S_{t-s} A_m S_s ds` to
  `D_m(t) = -(1 - m^{-t})/(log m) · V_m S_t` and `D̃_m(t) = -(1 - m^{-t}) V_m S_t` `(APS.8)`.

The semigroup is defined for all real `t` through `t⁺ = max t 0`, so `S_t = 1` for `t ≤ 0`.
-/

open scoped InnerProductSpace
open MeasureTheory Set HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- The arithmetic Hilbert space `ℓ²(ℕ≥1)`. -/
abbrev ArithSpace : Type := lp (fun _ : ℕ+ => ℂ) 2

/-- The coordinate vector `e_n`. -/
def basisVec (n : ℕ+) : ArithSpace := lp.single 2 n 1

theorem basisVec_eq_coordinateBasis (n : ℕ+) : basisVec n = ellTwoCoordinateBasis ℕ+ n := by
  rw [ellTwoCoordinateBasis_apply]
  rfl

theorem norm_basisVec (n : ℕ+) : ‖basisVec n‖ = 1 := by
  rw [basisVec_eq_coordinateBasis]
  exact (ellTwoCoordinateBasis ℕ+).orthonormal.1 n

theorem orthonormal_basisVec : Orthonormal ℂ basisVec := by
  have h := (ellTwoCoordinateBasis ℕ+).orthonormal
  have he : (ellTwoCoordinateBasis ℕ+ : ℕ+ → ArithSpace) = basisVec :=
    funext fun n => (basisVec_eq_coordinateBasis n).symm
  rwa [he] at h

/-- Bounded operators on `ℓ²(ℕ≥1)` agree once they agree on the coordinate vectors. -/
theorem ext_basisVec {A B : ArithSpace →L[ℂ] ArithSpace}
    (h : ∀ n, A (basisVec n) = B (basisVec n)) :
    A = B := by
  ext1 x
  have hx := (ellTwoCoordinateBasis ℕ+).hasSum_repr x
  have hA := hx.mapL A
  have hB := hx.mapL B
  simp only [map_smul, ← basisVec_eq_coordinateBasis, h] at hA hB
  exact hA.unique hB

/-! ### Multiplicative shifts -/

theorem mulLeft_injective (m : ℕ+) : Function.Injective (fun n : ℕ+ => m * n) :=
  fun _ _ h => mul_left_cancel h

/-- The multiplicative isometry `V_m e_n = e_{mn}` `(APS.3)`. -/
def shift (m : ℕ+) : ArithSpace →L[ℂ] ArithSpace :=
  (lpScalarInjection (fun n : ℕ+ => m * n) (mulLeft_injective m)).toContinuousLinearMap

theorem shift_basisVec (m n : ℕ+) : shift m (basisVec n) = basisVec (m * n) :=
  lpScalarInjection_single _ (mulLeft_injective m) n 1

theorem norm_shift_apply (m : ℕ+) (x : ArithSpace) : ‖shift m x‖ = ‖x‖ :=
  (lpScalarInjection (fun n : ℕ+ => m * n) (mulLeft_injective m)).norm_map x

/-- `V_m V_n = V_{mn}`: multiplicative endpoints commute. -/
theorem shift_mul (m n : ℕ+) : shift m * shift n = shift (m * n) :=
  ext_basisVec fun k => by
    simp only [mul_apply_eq_comp, shift_basisVec, mul_assoc]

theorem shift_comm (m n : ℕ+) : shift m * shift n = shift n * shift m := by
  rw [shift_mul, shift_mul, mul_comm]

/-- The vacuum `e_1` is cyclic for the shift algebra: `V_n e_1 = e_n`. -/
theorem shift_vacuum (n : ℕ+) : shift n (basisVec 1) = basisVec n := by
  rw [shift_basisVec, mul_one]

/-! ### The heat semigroup -/

/-- The heat weight `n^{-t⁺}`. -/
def heatWeight (t : ℝ) (n : ℕ+) : ℂ := (((n : ℕ) : ℝ) ^ (-max t 0) : ℝ)

theorem norm_heatWeight_le (t : ℝ) (n : ℕ+) : ‖heatWeight t n‖ ≤ 1 := by
  rw [heatWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos)
    (neg_nonpos.mpr (le_max_right _ _))

/-- The heat semigroup `S_t e_n = n^{-t} e_n` `(APS.2)`. -/
def heat (t : ℝ) : ArithSpace →L[ℂ] ArithSpace :=
  ellTwoDiagonal (heatWeight t) (norm_heatWeight_le t)

theorem heat_basisVec (t : ℝ) (n : ℕ+) : heat t (basisVec n) = heatWeight t n • basisVec n := by
  rw [basisVec_eq_coordinateBasis]
  exact ellTwoDiagonal_coordinateBasis _ _ n

theorem heatWeight_of_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ+) :
    heatWeight t n = (((n : ℕ) : ℝ) ^ (-t) : ℝ) := by
  rw [heatWeight, max_eq_left ht]

theorem heatWeight_one (t : ℝ) : heatWeight t 1 = 1 := by
  simp [heatWeight]

theorem heat_vacuum (t : ℝ) : heat t (basisVec 1) = basisVec 1 := by
  rw [heat_basisVec, heatWeight_one, one_smul]

theorem norm_heat_le (t : ℝ) : ‖heat t‖ ≤ 1 :=
  norm_ellTwoDiagonal_le _ _ zero_le_one

theorem heat_zero : heat 0 = 1 :=
  ext_basisVec fun n => by simp [heat_basisVec, heatWeight]

/-- The semigroup law `S_{s+t} = S_s S_t`, `s, t ≥ 0`. -/
theorem heat_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : heat (s + t) = heat s * heat t :=
  ext_basisVec fun n => by
    have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have hw : heatWeight (s + t) n = heatWeight t n * heatWeight s n := by
      rw [heatWeight_of_nonneg (add_nonneg hs ht), heatWeight_of_nonneg hs,
        heatWeight_of_nonneg ht, ← Complex.ofReal_mul, ← Real.rpow_add hn, neg_add, add_comm]
    rw [heat_basisVec, mul_apply_eq_comp, heat_basisVec, map_smul, heat_basisVec, smul_smul, hw]

/-- **`(APS.7)`: intertwining** `S_t V_m = m^{-t} V_m S_t`, `t ≥ 0`. -/
theorem heat_mul_shift {t : ℝ} (ht : 0 ≤ t) (m : ℕ+) :
    heat t * shift m = ((((m : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ) • (shift m * heat t) :=
  ext_basisVec fun n => by
    simp only [mul_apply_eq_comp, smul_apply, shift_basisVec,
      heat_basisVec, map_smul, smul_smul]
    rw [heatWeight_of_nonneg ht, heatWeight_of_nonneg ht, ← Complex.ofReal_mul, PNat.mul_coe,
      Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-! ### The logarithmic generator on the finite-support core -/

/-- The finite-support core embedded in `ℓ²(ℕ≥1)`. -/
def coreEmbed : (ℕ+ →₀ ℂ) →ₗ[ℂ] ArithSpace := Finsupp.linearCombination ℂ basisVec

/-- The logarithmic generator `L e_n = (log n) e_n` on the core `(APS.1)`. -/
def logGen : (ℕ+ →₀ ℂ) →ₗ[ℂ] (ℕ+ →₀ ℂ) :=
  Finsupp.lsum ℂ fun n : ℕ+ => ((Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) • Finsupp.lsingle n

/-- The multiplicative shift on the core. -/
def coreShift (m : ℕ+) : (ℕ+ →₀ ℂ) →ₗ[ℂ] (ℕ+ →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun n : ℕ+ => m * n)

theorem logGen_single (n : ℕ+) (c : ℂ) :
    logGen (Finsupp.single n c) = Finsupp.single n ((Real.log ((n : ℕ) : ℝ) : ℂ) * c) := by
  simp [logGen, Finsupp.smul_single, smul_eq_mul]

theorem coreShift_single (m n : ℕ+) (c : ℂ) :
    coreShift m (Finsupp.single n c) = Finsupp.single (m * n) c := by
  simp [coreShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem coreEmbed_single (n : ℕ+) (c : ℂ) : coreEmbed (Finsupp.single n c) = c • basisVec n := by
  simp [coreEmbed]

/-- The core shift is the restriction of `V_m`. -/
theorem coreEmbed_coreShift (m : ℕ+) (f : ℕ+ →₀ ℂ) :
    coreEmbed (coreShift m f) = shift m (coreEmbed f) := by
  have h : coreEmbed ∘ₗ coreShift m = (shift m : ArithSpace →ₗ[ℂ] ArithSpace) ∘ₗ coreEmbed :=
    Finsupp.lhom_ext fun n c => by
      simp [coreShift_single, coreEmbed_single, shift_basisVec]
  exact congrArg (fun φ : (ℕ+ →₀ ℂ) →ₗ[ℂ] ArithSpace => φ f) h

/-- **`(APS.4)`: the source commutator** `[L, V_m] = (log m) V_m` on the core. -/
theorem logGen_commutator (m : ℕ+) (f : ℕ+ →₀ ℂ) :
    logGen (coreShift m f) - coreShift m (logGen f) =
      (Real.log ((m : ℕ) : ℝ) : ℂ) • coreShift m f := by
  have h : logGen ∘ₗ coreShift m - coreShift m ∘ₗ logGen =
      (Real.log ((m : ℕ) : ℝ) : ℂ) • coreShift m :=
    Finsupp.lhom_ext fun n c => by
      have hm : (0 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast m.pos
      have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        coreShift_single, logGen_single, Finsupp.smul_single, smul_eq_mul]
      rw [← Finsupp.single_sub, PNat.mul_coe, Nat.cast_mul, Real.log_mul hm.ne' hn.ne']
      congr 1
      push_cast
      ring
  exact congrArg (fun φ : (ℕ+ →₀ ℂ) →ₗ[ℂ] (ℕ+ →₀ ℂ) => φ f) h

/-- The source-normalized letter `A_m = (log m) V_m` `(APS.5)`. -/
def letter (m : ℕ+) : ArithSpace →L[ℂ] ArithSpace := (Real.log ((m : ℕ) : ℝ) : ℂ) • shift m

/-- `(APS.5)`: the commutator extends to the bounded operator `A_m`. -/
theorem coreEmbed_commutator (m : ℕ+) (f : ℕ+ →₀ ℂ) :
    coreEmbed (logGen (coreShift m f) - coreShift m (logGen f)) = letter m (coreEmbed f) := by
  rw [logGen_commutator, map_smul, coreEmbed_coreShift, letter, smul_apply]

/-- The semigroup is generated by `-L` on the coordinate vectors. -/
theorem hasDerivAt_heat_basisVec {t : ℝ} (ht : 0 < t) (n : ℕ+) :
    HasDerivAt (fun s => heat s (basisVec n))
      (-(Real.log ((n : ℕ) : ℝ) : ℂ) • heat t (basisVec n)) t := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hw : ∀ᶠ s in nhds t, heat s (basisVec n) =
      ((((n : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) • basisVec n := by
    filter_upwards [lt_mem_nhds ht] with s hs
    rw [heat_basisVec, heatWeight_of_nonneg hs.le]
  have hd : HasDerivAt (fun s : ℝ => (((n : ℕ) : ℝ) ^ (-s) : ℝ))
      ((((n : ℕ) : ℝ) ^ (-t)) * Real.log ((n : ℕ) : ℝ) * (-1)) t :=
    (Real.hasStrictDerivAt_const_rpow hn (-t)).hasDerivAt.comp t (hasDerivAt_neg t)
  have hd' := (hd.ofReal_comp).smul_const (basisVec n)
  refine (hd'.congr_of_eventuallyEq hw).congr_deriv ?_
  rw [heat_basisVec, heatWeight_of_nonneg ht.le, smul_smul]
  congr 1
  push_cast
  ring

/-! ### One-letter Duhamel responses -/

/-- The Duhamel response `-∫₀ᵗ S_{t-s} X S_s ds` of an intervention letter `X` `(APS.6)`. -/
def duhamel (X : ArithSpace →L[ℂ] ArithSpace) (t : ℝ) : ArithSpace →L[ℂ] ArithSpace :=
  -∫ s in (0 : ℝ)..t, heat (t - s) * X * heat s

theorem integral_rpow_neg_sub {m : ℝ} (hm : 1 < m) {t : ℝ} :
    ∫ s in (0 : ℝ)..t, m ^ (-(t - s)) = (1 - m ^ (-t)) / Real.log m := by
  have hm0 : 0 < m := by linarith
  have hlog : 0 < Real.log m := Real.log_pos hm
  have hfun : (fun s : ℝ => m ^ (-(t - s))) = fun s => m ^ (s - t) := by
    funext s
    rw [neg_sub]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => m ^ (s - t) / Real.log m)
      (m ^ (s - t)) s := fun s _ => by
    have h := (Real.hasStrictDerivAt_const_rpow hm0 (s - t)).hasDerivAt.comp s
      ((hasDerivAt_id s).sub_const t)
    refine (h.div_const (Real.log m)).congr_deriv ?_
    field_simp
  have hcont : Continuous fun s : ℝ => m ^ (s - t) :=
    continuous_const.rpow (by fun_prop) fun _ => Or.inl hm0.ne'
  rw [hfun, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [sub_self, Real.rpow_zero, zero_sub]
  ring

/-- **`(APS.8)`, raw response**: `D_m(t) = -(1 - m^{-t})/(log m) · V_m S_t`. -/
theorem duhamel_shift {t : ℝ} (ht : 0 ≤ t) {m : ℕ+} (hm : 2 ≤ (m : ℕ)) :
    duhamel (shift m) t =
      -((((1 - ((m : ℕ) : ℝ) ^ (-t)) / Real.log ((m : ℕ) : ℝ) : ℝ) : ℂ) •
        (shift m * heat t)) := by
  have hm1 : (1 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast hm
  have hint : ∀ s ∈ uIcc (0 : ℝ) t, heat (t - s) * shift m * heat s =
      ((((m : ℕ) : ℝ) ^ (-(t - s)) : ℝ) : ℂ) • (shift m * heat t) := fun s hs => by
    rw [uIcc_of_le ht] at hs
    have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
    rw [heat_mul_shift hts, smul_mul_assoc, mul_assoc, ← heat_add hts hs.1, sub_add_cancel]
  rw [duhamel, intervalIntegral.integral_congr hint, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_ofReal, integral_rpow_neg_sub hm1]

/-- **`(APS.8)`, normalized response**: `D̃_m(t) = -(1 - m^{-t}) V_m S_t`. -/
theorem duhamel_letter {t : ℝ} (ht : 0 ≤ t) {m : ℕ+} (hm : 2 ≤ (m : ℕ)) :
    duhamel (letter m) t = -((((1 - ((m : ℕ) : ℝ) ^ (-t)) : ℝ) : ℂ) • (shift m * heat t)) := by
  have hm1 : (1 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast hm
  have hlog : Real.log ((m : ℕ) : ℝ) ≠ 0 := (Real.log_pos hm1).ne'
  have h : duhamel (letter m) t = (Real.log ((m : ℕ) : ℝ) : ℂ) • duhamel (shift m) t := by
    simp only [duhamel, letter, mul_smul_comm, smul_mul_assoc, smul_neg]
    rw [intervalIntegral.integral_smul]
  rw [h, duhamel_shift ht hm, smul_neg, smul_smul, ← Complex.ofReal_mul,
    mul_div_cancel₀ _ hlog]

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
