import GaloisForLFunctions.HTGeometry.JetTopDescentTower
import GaloisForLFunctions.HTGeometry.JetShiftAffinePresentation

/-!
# The top coefficient of a normalizing shift, uniformly in the level

The partial of the shift in the coordinate just below the top is the same at every level up to the
level itself:

`∂_M σ_{M+1} = (M + 1)·δ(R'(y₀))`,

by induction along the shift recursion, the commutator `[∂_{m+1}, δ] = ∂_m`, and the fact that
`δ(R'(y₀))` has jet order one.  In weight-zero coordinates this says that the descent of the shift
is the constant `(M + 1)·R''(y₀)` and that its second descent vanishes.

Consequently a normalizing shift at any level `N + 1 ≥ 4` is affine in its top coordinate, with top
coefficient pinned to `−(N + 1)·z₂`: the descent tower turns the shift relation into a relation of
exponent two for the first descent, which the affine-coefficient rigidity solves, and into a pure
eigen-relation of exponent `2 − N` for the second, which eigen-rigidity kills.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-! ## The partial of the shift below the top -/

/-- **The subtop partial of the shift.**  At every level it is the level times the ambient
derivative of the derivative factor. -/
theorem pd_subtop_substitutionShift (R : RatFunc C) {M : ℕ} (hM : 1 ≤ M) :
    JetField.pd ((), M) (substitutionShift R (M + 1))
      = ((M + 1 : ℕ) : JetField C Unit) * JetField.jetDerivation (substitutionDeriv R) := by
  have hδρ : JetField.jetDerivation (substitutionDeriv R)
      = JetField.jet ((), 1) * JetField.pd ((), 0) (substitutionDeriv R) :=
    jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)
  induction M, hM using Nat.le_induction with
  | base =>
      have hσ2 : substitutionShift R 2
          = JetField.pd ((), 0) (substitutionDeriv R)
            * (JetField.jet ((), 1) : JetField C Unit) ^ 2 := substitutionShift_two R
      have hpd0 : JetField.pd ((), 1) (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
        rw [pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
      have hleib := (JetField.pd ((), 1) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (JetField.pd ((), 0) (substitutionDeriv R))
          ((JetField.jet ((), 1) : JetField C Unit) ^ 2)
      simp only [smul_eq_mul] at hleib
      have hpow : JetField.pd ((), 1) ((JetField.jet ((), 1) : JetField C Unit) ^ 2)
          = 2 * (JetField.jet ((), 1) : JetField C Unit) := by
        have hl := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
            (JetField.jet ((), 1) : JetField C Unit) 2
        rw [JetField.pd_jet_self] at hl
        rw [hl]
        simp
      rw [show (1 : ℕ) + 1 = 2 from rfl, hσ2, hleib, hpd0, hpow, hδρ]
      push_cast
      ring
  | succ M hM ih =>
      have hrec := substitutionShift_succ R (M + 1)
      have hcomm := pd_jetDerivation_apply (C := C) M (substitutionShift R (M + 1))
      have htop : JetField.pd ((), M + 1) (substitutionShift R (M + 1)) = 0 :=
        (mem_jetPrefixField_iff (M + 1) _).mp
          (substitutionShift_mem_jetPrefixField R (by omega)) (M + 1) (le_refl _)
      have hδρtop : JetField.pd ((), M + 1)
          (JetField.jetDerivation (substitutionDeriv R)) = 0 :=
        pd_jetDerivation_substitutionDeriv R (by omega)
      have hleib := (JetField.pd ((), M + 1) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (JetField.jet ((), 1) * JetField.pd ((), 0) (substitutionDeriv R))
          (JetField.jet ((), M + 1) : JetField C Unit)
      simp only [smul_eq_mul] at hleib
      rw [← hδρ] at hleib
      rw [hrec, map_add, ← hδρ, hleib, hδρtop, JetField.pd_jet_self, mul_one, mul_zero,
        add_zero, hcomm, htop, map_zero, zero_add, ih]
      push_cast
      ring

/-! ## The descent of the shift -/

theorem topDescent_substitutionShiftRatio (R : RatFunc C) {M : ℕ} (hM : 2 ≤ M) :
    topDescent M (substitutionShiftRatio R (M + 1))
      = ((M + 1 : ℕ) : JetField C Unit) * JetField.pd ((), 0) (substitutionDeriv R) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hδρ : JetField.jetDerivation (substitutionDeriv R)
      = JetField.jet ((), 1) * JetField.pd ((), 0) (substitutionDeriv R) :=
    jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)
  have hmul : substitutionShiftRatio R (M + 1)
      * (JetField.jet ((), 1) : JetField C Unit) ^ (M + 1) = substitutionShift R (M + 1) := by
    rw [substitutionShiftRatio]
    field_simp
  have hpow : JetField.pd ((), M) ((JetField.jet ((), 1) : JetField C Unit) ^ (M + 1)) = 0 := by
    have hl := (JetField.pd ((), M) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
        (JetField.jet ((), 1) : JetField C Unit) (M + 1)
    rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
    simpa using hl
  have hleib := (JetField.pd ((), M) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionShiftRatio R (M + 1)) ((JetField.jet ((), 1) : JetField C Unit) ^ (M + 1))
  simp only [smul_eq_mul] at hleib
  rw [hmul, hpow, mul_zero, zero_add, pd_subtop_substitutionShift R (by omega), hδρ] at hleib
  rw [topDescent]
  refine mul_left_cancel₀ hy1 ?_
  calc (JetField.jet ((), 1) : JetField C Unit)
        * ((JetField.jet ((), 1) : JetField C Unit) ^ M
          * JetField.pd ((), M) (substitutionShiftRatio R (M + 1)))
      = (JetField.jet ((), 1) : JetField C Unit) ^ (M + 1)
        * JetField.pd ((), M) (substitutionShiftRatio R (M + 1)) := by
        rw [pow_succ]; ring
    _ = ((M + 1 : ℕ) : JetField C Unit)
        * ((JetField.jet ((), 1) : JetField C Unit)
          * JetField.pd ((), 0) (substitutionDeriv R)) := hleib.symm
    _ = (JetField.jet ((), 1) : JetField C Unit)
        * (((M + 1 : ℕ) : JetField C Unit)
          * JetField.pd ((), 0) (substitutionDeriv R)) := by ring

theorem topDescent_topDescent_substitutionShiftRatio (R : RatFunc C) {M : ℕ} (hM : 2 ≤ M) :
    (topDescent (C := C) M)^[2] (substitutionShiftRatio R (M + 1)) = 0 := by
  have hpd0 : JetField.pd ((), M) (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
    rw [pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
  have h1 : (topDescent (C := C) M)^[2] (substitutionShiftRatio R (M + 1))
      = topDescent M (topDescent M (substitutionShiftRatio R (M + 1))) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  rw [h1, topDescent_substitutionShiftRatio R hM, topDescent]
  have hleib := (JetField.pd ((), M) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (((M + 1 : ℕ) : JetField C Unit)) (JetField.pd ((), 0) (substitutionDeriv R))
  simp only [smul_eq_mul] at hleib
  have hcast : JetField.pd ((), M) (((M + 1 : ℕ) : JetField C Unit)) = 0 := by
    rw [show (((M + 1 : ℕ) : JetField C Unit))
        = algebraMap C (JetField C Unit) (((M + 1 : ℕ) : C)) from
      (map_natCast (algebraMap C (JetField C Unit)) (M + 1)).symm,
      Derivation.map_algebraMap]
  rw [hleib, hpd0, hcast, mul_zero, mul_zero, add_zero, mul_zero]

/-! ## The torus and the descent -/

theorem isWeightZero_topDescent {N : ℕ} {v : JetField C Unit} (hv : IsWeightZero v) :
    IsWeightZero (topDescent N v) := by
  have h2 : (2 : C) ≠ 0 := two_ne_zero
  have hpd := weightScale_pd (C := C) h2 N v
  rw [show weightScale h2 v = v from hv] at hpd
  show weightScale h2 (topDescent N v) = topDescent N v
  rw [topDescent, map_mul, map_pow, weightScale_jet]
  conv_rhs => rw [hpd]
  rw [mul_pow, ← map_pow, ← pow_mul, one_mul]
  ring

/-! ## The top coefficient of a normalizing shift -/

/-- **The top coefficient of a normalizing shift, at every level.**  A weight-zero solution of the
shift relation at level `N + 1` is affine in its top coordinate, and the coefficient is `−(N+1)·z₂`
independently of the level. -/
theorem topDescent_of_zshift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ} (hN : 3 ≤ N)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (hord : ∀ j : ℕ, N < j → JetField.pd ((), j) w = 0)
    (heq : substitutionDeriv R ^ (N + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (N + 1)) :
    topDescent N w
        = -(algebraMap C (JetField C Unit) (((N + 1 : ℕ) : C))
          * (jetRatio 2 : JetField C Unit))
      ∧ (topDescent (C := C) N)^[2] w = 0 := by
  have hNle : 1 ≤ N := by omega
  have hzeq : substitutionDeriv R ^ (((N + 1 : ℕ) : ℤ)) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (N + 1) := by
    rw [zpow_natCast]
    exact heq
  have htower := jetSubstitution_topDescent_iterate R hR hNle hord hzeq
  -- the first descent
  have h1 := htower 1
  simp only [Function.iterate_one] at h1
  rw [topDescent_substitutionShiftRatio R (by omega)] at h1
  have hexp1 : ((N + 1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) * (1 - (N : ℤ)) = ((2 : ℕ) : ℤ) := by
    push_cast; ring
  rw [hexp1, zpow_natCast] at h1
  have hmC : ((N + 1 : ℕ) : JetField C Unit)
      = algebraMap C (JetField C Unit) (((N + 1 : ℕ) : C)) :=
    (map_natCast (algebraMap C (JetField C Unit)) (N + 1)).symm
  rw [hmC] at h1
  have hlin := eq_neg_mul_jetRatio_two_of_linear R hR (K := N) (by omega) hfix
    (isWeightZero_topDescent hwz) (topDescent_order hNle hord) h1
  refine ⟨hlin, ?_⟩
  -- the second descent
  have h2 := htower 2
  rw [topDescent_topDescent_substitutionShiftRatio R (by omega), sub_zero] at h2
  have hexp2 : ((N + 1 : ℕ) : ℤ) + ((2 : ℕ) : ℤ) * (1 - (N : ℤ)) = (3 : ℤ) - (N : ℤ) := by
    push_cast; ring
  rw [hexp2] at h2
  by_contra hne
  have hord2 : ∀ j : ℕ, N < j →
      JetField.pd ((), j) ((topDescent (C := C) N)^[2] w) = 0 :=
    topDescent_iterate_order hNle hord 2
  have hwz2 : IsWeightZero ((topDescent (C := C) N)^[2] w) := by
    have h0 : (topDescent (C := C) N)^[2] w = topDescent N (topDescent N w) := by
      rw [Function.iterate_succ_apply', Function.iterate_one]
    rw [h0]
    exact isWeightZero_topDescent (isWeightZero_topDescent hwz)
  have heig : substitutionDeriv R ^ ((2 : ℤ) - (N : ℤ))
      * jetSubstitution R hR ((topDescent (C := C) N)^[2] w)
      = (topDescent (C := C) N)^[2] w := by
    refine mul_left_cancel₀ hR ?_
    rw [← mul_assoc, ← zpow_one_add₀ hR]
    rw [show (1 : ℤ) + ((2 : ℤ) - (N : ℤ)) = (3 : ℤ) - (N : ℤ) from by ring]
    exact h2
  have := exponent_eq_zero_of_weightZero_eigen R hR (K := N) (by omega) hfix hwz2 hne hord2 heig
  omega

end

end GaloisForLFunctions.HTGeometry
