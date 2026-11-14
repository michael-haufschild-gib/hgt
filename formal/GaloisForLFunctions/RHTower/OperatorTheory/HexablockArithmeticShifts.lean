import GaloisForLFunctions.HTGeometry.OperatorTheory.TetrablockAlgebra
import GaloisForLFunctions.HTGeometry.OperatorTheory.HexablockAlgebra
import GaloisForLFunctions.RHTower.PaperPrimeCoShiftEscape

/-!
# Hexablock coordinates of multiplicative arithmetic shifts

Every four positive-integer shifts satisfy the energy and cross-coordinate
identities of the hexablock parametrization. The Brown–Halmos slice for each
shift is exactly invariance under multiplicative translation. A compact
operator invariant under a single prime slice vanishes: prime powers escape
every finite set of arithmetic coordinates.
-/

noncomputable section
namespace RHTower.PrimeCoShift
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.Hexablock
open ContinuousLinearMap Filter Topology
open scoped InnerProductSpace

/-- Multiplicative arithmetic shifts represent the multiplicative monoid of positive integers. -/
theorem Vop_mul (p q : ℕ+) : Vop (p * q) = Vop p * Vop q := by
  apply star_injective
  simp only [star_Vop, star_mul]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext m
  change x ((p * q) * m) = x (p * (q * m))
  rw [mul_assoc]

@[simp] theorem Vop_one : Vop 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext m
  simpa only [one_mul] using Vop_apply_mul 1 x m

/-- Powers of a shift are shifts by powers of its positive-integer multiplier. -/
theorem Vop_pow (p : ℕ+) (n : ℕ) : Vop (p ^ n) = Vop p ^ n := by
  induction n with
  | zero => simp only [pow_zero, Vop_one]
  | succ n ih => rw [pow_succ, Vop_mul, ih, pow_succ]

/-- The powers of any prime shift eventually vanish in each fixed coordinate. -/
theorem primeShiftPowers_coordinate (p : Nat.Primes) (v : H) (m : ℕ+) :
    ∀ᶠ n in atTop, Vop (primePNat p ^ n) v m = 0 := by
  have hp : Tendsto (fun n : ℕ => (p : ℕ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt p.property.one_lt
  filter_upwards [hp.eventually (eventually_gt_atTop (m : ℕ))] with n hn
  apply Vop_apply_of_not_dvd
  intro hd
  have hle := Nat.le_of_dvd m.property hd
  exact (not_le_of_gt hn) hle

/-- Every orbit of a prime shift is weakly null. -/
theorem primeShiftPowers_weak_tendsto (p : Nat.Primes) (v z : H) :
    Tendsto (fun n => ⟪z, Vop (primePNat p ^ n) v⟫_ℂ) atTop (𝓝 0) := by
  apply tendsto_inner_lp_of_coord _ (norm_nonneg v)
    (fun n => ((primeShift (primePNat p ^ n)).norm_map v).le)
  intro m
  exact tendsto_const_nhds.congr' (primeShiftPowers_coordinate p v m).symm

/-- Compact operators kill every prime-shift orbit in norm. -/
theorem primeShiftPowers_compact_tendsto (p : Nat.Primes)
    (K : compactOperatorStarAlgebra H) (v : H) :
    Tendsto (fun n => K.1 (Vop (primePNat p ^ n) v)) atTop (𝓝 0) := by
  let C : ℝ := ‖v‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let u : H := ((C⁻¹ : ℝ) : ℂ) • v
  have hu : ‖u‖ ≤ 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hC]
    rw [inv_mul_le_iff₀ hC, mul_one]
    dsimp [C]
    linarith only [norm_nonneg v]
  have huv : (C : ℂ) • u = v := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hC.ne',
      Complex.ofReal_one, one_smul]
  have ht := tendsto_norm_compact_of_weaklyNull K.1 K.2
    (fun n => Vop (primePNat p ^ n) u)
    (fun n => ((primeShift (primePNat p ^ n)).norm_map u).le.trans hu)
    (fun z => primeShiftPowers_weak_tendsto p u z)
  have hs := (tendsto_const_nhds (x := (C : ℂ))).smul ht
  simpa only [← map_smul, huv, smul_zero] using hs

/-- A single prime's Brown–Halmos slice already excludes every nonzero compact operator. -/
theorem hexablock_prime_compact_iff (p : Nat.Primes) (T : H →L[ℂ] H) :
    (BrownHalmos (halfDiff (Vop (primePNat p)) 1) (halfSum (Vop (primePNat p)) 1)
      (halfSum (Vop (primePNat p)) 1) (Vop (primePNat p)) T ∧ IsCompactOperator T) ↔ T = 0 := by
  rw [slice_brownHalmos_iff]
  constructor
  · rintro ⟨hfix, hc⟩
    have hpow (n : ℕ) : star (Vop (primePNat p) ^ n) * T * Vop (primePNat p) ^ n = T := by
      induction n with
      | zero => simp only [pow_zero, star_one, one_mul, mul_one]
      | succ n ih =>
        rw [pow_succ, star_mul]
        calc
          star (Vop (primePNat p)) * star (Vop (primePNat p) ^ n) * T *
              (Vop (primePNat p) ^ n * Vop (primePNat p)) =
            star (Vop (primePNat p)) *
              (star (Vop (primePNat p) ^ n) * T * Vop (primePNat p) ^ n) *
                Vop (primePNat p) := by simp only [mul_assoc]
          _ = T := by rw [ih, hfix]
    apply ContinuousLinearMap.ext
    intro x
    rw [zero_apply]
    apply ext_inner_left ℂ
    intro y
    rw [inner_zero_right]
    have heq (n : ℕ) : ⟪y, T x⟫_ℂ =
        ⟪Vop (primePNat p ^ n) y, T (Vop (primePNat p ^ n) x)⟫_ℂ := by
      have hp := hpow n
      rw [← Vop_pow] at hp
      conv_lhs => rw [← hp]
      change ⟪y, (star (Vop (primePNat p ^ n))) (T (Vop (primePNat p ^ n) x))⟫_ℂ = _
      rw [_root_.ContinuousLinearMap.star_eq_adjoint, adjoint_inner_right]
    have ht : Tendsto (fun n =>
        ⟪Vop (primePNat p ^ n) y, T (Vop (primePNat p ^ n) x)⟫_ℂ) atTop (𝓝 0) := by
      have hb := (primeShiftPowers_compact_tendsto p ⟨T, hc⟩ x).norm.const_mul ‖y‖
      rw [norm_zero, mul_zero] at hb
      refine squeeze_zero_norm (fun n => ?_) hb
      calc
        ‖⟪Vop (primePNat p ^ n) y, T (Vop (primePNat p ^ n) x)⟫_ℂ‖ ≤
            ‖Vop (primePNat p ^ n) y‖ * ‖T (Vop (primePNat p ^ n) x)‖ :=
          norm_inner_le_norm _ _
        _ = ‖y‖ * ‖T (Vop (primePNat p ^ n) x)‖ := by
          rw [show ‖Vop (primePNat p ^ n) y‖ = ‖y‖ from (primeShift _).norm_map y]
    exact tendsto_nhds_unique (tendsto_const_nhds.congr heq) ht
  · rintro rfl
    exact ⟨by simp only [mul_zero, zero_mul], isCompactOperator_zero⟩


private theorem shift_isometry (p : ℕ+) : star (Vop p) * Vop p = 1 := by
  rw [star_Vop, coShift_mul_Vop]

/-- The hexablock energy and cross-coordinate identities for arbitrary arithmetic shifts. -/
theorem hexablock_arithmetic_relations (p q r s : ℕ+) :
    (star (a (Vop p) (Vop r)) * a (Vop p) (Vop r) +
      star (x₁ (Vop p) (Vop q)) * x₁ (Vop p) (Vop q) = 1) ∧
    (star (a (Vop p) (Vop r)) * a (Vop p) (Vop r) +
      star (x₂ (Vop p) (Vop r) (Vop s)) * x₂ (Vop p) (Vop r) (Vop s) = 1) ∧
    star (x₃ (Vop p) (Vop q) (Vop r) (Vop s)) *
      x₃ (Vop p) (Vop q) (Vop r) (Vop s) = 1 ∧
    star (x₁ (Vop p) (Vop q)) * x₃ (Vop p) (Vop q) (Vop r) (Vop s) =
      x₂ (Vop p) (Vop r) (Vop s) := by
  obtain ⟨h₁, h₂, h₃⟩ := energy _ _ _ _
    (shift_isometry p) (shift_isometry q) (shift_isometry r) (shift_isometry s)
  exact ⟨h₁, h₂, h₃, cross _ _ _ _ (shift_isometry p) (shift_isometry q)
    (Vop_commute p q) (Vop_commute p r) (Vop_commute p s)⟩

/-- Brown–Halmos equations on one arithmetic slice are multiplicative translation invariance. -/
theorem hexablock_arithmetic_brownHalmos_iff (p : ℕ+) (T : H →L[ℂ] H) :
    BrownHalmos (halfDiff (Vop p) 1) (halfSum (Vop p) 1)
      (halfSum (Vop p) 1) (Vop p) T ↔ primeCoShift p * T * Vop p = T := by
  rw [slice_brownHalmos_iff, star_Vop]

/-- Compact arithmetic Brown–Halmos operators vanish; no symbol representation is assumed. -/
theorem hexablock_arithmetic_compact_iff (T : H →L[ℂ] H) :
    ((∀ p : ℕ+, BrownHalmos (halfDiff (Vop p) 1) (halfSum (Vop p) 1)
      (halfSum (Vop p) 1) (Vop p) T) ∧ IsCompactOperator T) ↔ T = 0 := by
  constructor
  · rintro ⟨hfix, hc⟩
    exact (hexablock_prime_compact_iff ⟨2, Nat.prime_two⟩ T).mp ⟨hfix _, hc⟩
  · rintro rfl
    refine ⟨fun p => (slice_brownHalmos_iff (Vop p) 0).mpr ?_, isCompactOperator_zero⟩
    simp only [mul_zero, zero_mul]

/-- Three arithmetic shifts give the tetrablock cross relation and complementary energy. -/
theorem tetrablock_arithmetic_relations (p q r : ℕ+) :
    (star (halfDiff (Vop p) (Vop q)) * halfDiff (Vop p) (Vop q) +
      star (Tetrablock.x₂ (Vop p) (Vop q)) * Tetrablock.x₂ (Vop p) (Vop q) = 1) ∧
    (star (Tetrablock.x₂ (Vop p) (Vop q)) * Tetrablock.x₃ (Vop p) (Vop q) (Vop r) =
      Tetrablock.x₁ (Vop p) (Vop q) (Vop r)) ∧
    star (Tetrablock.x₃ (Vop p) (Vop q) (Vop r)) * Tetrablock.x₃ (Vop p) (Vop q) (Vop r) = 1 := by
  exact ⟨Tetrablock.energy _ _ (shift_isometry p) (shift_isometry q),
    Tetrablock.cross _ _ _ (shift_isometry p) (shift_isometry q)
      (Vop_commute p q) (Vop_commute p r) (Vop_commute q r),
    Tetrablock.last_isometry _ _ _ (shift_isometry p) (shift_isometry q) (shift_isometry r)⟩

end RHTower.PrimeCoShift

#print axioms RHTower.PrimeCoShift.hexablock_arithmetic_relations
#print axioms RHTower.PrimeCoShift.hexablock_arithmetic_brownHalmos_iff
#print axioms RHTower.PrimeCoShift.hexablock_arithmetic_compact_iff

#print axioms RHTower.PrimeCoShift.tetrablock_arithmetic_relations

#print axioms RHTower.PrimeCoShift.hexablock_prime_compact_iff
