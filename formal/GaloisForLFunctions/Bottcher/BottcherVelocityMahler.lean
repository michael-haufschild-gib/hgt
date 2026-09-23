import GaloisForLFunctions.HTGeometry.GapSeriesIrrational
import GaloisForLFunctions.HTGeometry.MahlerHomogeneousRigidity
import GaloisForLFunctions.HTGeometry.FormalMahlerDescent

/-!
# The Böttcher velocity series is the unique solution of its Mahler equation

The dyadic series `A = ∑_{j≥0} X^{2^{j+1}}/2^{j+1}` satisfies the inhomogeneous Mahler
equation `A(X²) = 2·A − X²` (`bottcherVelocitySeries_mahler`), and it is the **only** formal
power series doing so (`bottcherVelocity_mahler_unique`): the difference of two solutions
solves the homogeneous equation `D(X²) = 2·D`, which is rigid.  Combined with the support-gap
irrationality of `A`, both formal inputs of the order-one Mahler dichotomy are pinned on the
canonical solution of the Böttcher parameter-velocity constraint.
-/

open PowerSeries

namespace GaloisForLFunctions

/-- **The velocity series satisfies its Mahler equation**: `A(X²) = 2·A − X²`. -/
theorem bottcherVelocitySeries_mahler :
    subst (PowerSeries.X ^ (2 : ℕ)) bottcherVelocitySeries
      = PowerSeries.C (2 : ℂ) * bottcherVelocitySeries - PowerSeries.X ^ (2 : ℕ) := by
  ext n
  rw [PowerSeries.coeff_subst_X_pow (by norm_num : (2 : ℕ) ≠ 0), map_sub, coeff_C_mul,
    PowerSeries.coeff_X_pow]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m (by norm_num)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have ha0 : PowerSeries.coeff 0 bottcherVelocitySeries = 0 :=
        coeff_bottcherVelocitySeries_of_ne 0 (fun j => Nat.ne_of_lt (by positivity))
      norm_num [ha0]
    · rcases eq_or_ne m 1 with rfl | hm1
      · have ha1 : PowerSeries.coeff 1 bottcherVelocitySeries = 0 :=
          coeff_bottcherVelocitySeries_of_ne 1 (fun j => by
            have h4 : 2 ≤ 2 ^ (j + 1) := by
              calc (2 : ℕ) = 2 ^ (1 : ℕ) := by norm_num
                _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega)
        have ha2 : PowerSeries.coeff (2 * 1) bottcherVelocitySeries = (2 : ℂ)⁻¹ := by
          rw [show 2 * 1 = 2 ^ (0 + 1) by norm_num, coeff_bottcherVelocitySeries_pow 0]
          norm_num
        rw [ha1, ha2]
        norm_num
      · by_cases hpow : ∃ j : ℕ, m = 2 ^ (j + 1)
        · obtain ⟨j, rfl⟩ := hpow
          rw [coeff_bottcherVelocitySeries_pow j,
            show 2 * 2 ^ (j + 1) = 2 ^ (j + 1 + 1) by ring,
            coeff_bottcherVelocitySeries_pow (j + 1)]
          have hne2 : 2 ^ (j + 1 + 1) ≠ 2 := by
            have h4 : (4 : ℕ) ≤ 2 ^ (j + 1 + 1) := by
              calc (4 : ℕ) = 2 ^ (2 : ℕ) := by norm_num
                _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          rw [if_neg hne2, sub_zero]
          push_cast
          rw [pow_succ]
          have hne : ((2 : ℂ)) ^ (j + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
          field_simp
          ring
        · have hmne : ∀ j : ℕ, m ≠ 2 ^ (j + 1) := fun j hj => hpow ⟨j, hj⟩
          have h2m : ∀ j : ℕ, 2 * m ≠ 2 ^ (j + 1) := by
            intro j hj
            rcases Nat.eq_zero_or_pos j with rfl | hj0
            · norm_num at hj
              omega
            · apply hpow
              have hj' : 2 * m = 2 ^ j * 2 := by rw [hj, pow_succ]
              have hmj : m = 2 ^ j := by omega
              exact ⟨j - 1, by rw [hmj]; congr 1; omega⟩
          rw [coeff_bottcherVelocitySeries_of_ne m hmne,
            coeff_bottcherVelocitySeries_of_ne (2 * m) h2m,
            if_neg (by omega : 2 * m ≠ 2)]
          ring
  · rw [if_neg h2,
      coeff_bottcherVelocitySeries_of_ne n
        (fun j hj => h2 (by rw [hj]; exact dvd_pow_self 2 (Nat.succ_ne_zero j))),
      if_neg (fun h : n = 2 => h2 (by rw [h])), mul_zero, sub_zero]

/-- **Uniqueness**: the velocity series is the only formal solution of its Mahler equation —
no normalization needed, the homogeneous rigidity pins even the constant term. -/
theorem bottcherVelocity_mahler_unique {Y : ℂ⟦X⟧}
    (h : subst (PowerSeries.X ^ (2 : ℕ)) Y
      = PowerSeries.C (2 : ℂ) * Y - PowerSeries.X ^ (2 : ℕ)) :
    Y = bottcherVelocitySeries := by
  have hsub : subst (PowerSeries.X ^ (2 : ℕ)) (Y - bottcherVelocitySeries)
      = PowerSeries.C (2 : ℂ) * (Y - bottcherVelocitySeries) := by
    rw [← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0)), map_sub,
      PowerSeries.coe_substAlgHom, h, bottcherVelocitySeries_mahler]
    ring
  have h0 := mahler_homogeneous_eq_zero le_rfl two_ne_zero (by norm_num) hsub
  exact sub_eq_zero.mp h0

/-- **Derivative transfer.**  Differentiating the Mahler equation through the substitution
chain rule yields `X·A'(X²) = A' − X`: the dyadic transform of the derivative is recoverable
from the derivative itself — the triangular mechanism by which the second parameter jet
exposes the spatial derivative of the first. -/
theorem bottcherVelocity_deriv_transfer :
    PowerSeries.X * subst (PowerSeries.X ^ (2 : ℕ)) (d⁄dX ℂ bottcherVelocitySeries)
      = d⁄dX ℂ bottcherVelocitySeries - PowerSeries.X := by
  have hC2 : PowerSeries.C (2 : ℂ) = (2 : ℂ⟦X⟧) := map_ofNat _ 2
  have h20 : (2 : ℂ⟦X⟧) ≠ 0 := by
    intro hh
    rw [← hC2] at hh
    have h0 := congrArg (PowerSeries.coeff 0) hh
    simp at h0
  have h := congrArg (⇑(d⁄dX ℂ)) bottcherVelocitySeries_mahler
  rw [PowerSeries.derivative_subst ℂ (PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0)),
    map_sub] at h
  have hCA : d⁄dX ℂ (PowerSeries.C (2 : ℂ) * bottcherVelocitySeries)
      = PowerSeries.C (2 : ℂ) * d⁄dX ℂ bottcherVelocitySeries := by
    rw [Derivation.leibniz, PowerSeries.derivative_C]
    simp [smul_eq_mul]
  have hX2 : d⁄dX ℂ (PowerSeries.X ^ (2 : ℕ) : ℂ⟦X⟧) = 2 * PowerSeries.X := by
    rw [pow_two, Derivation.leibniz, PowerSeries.derivative_X]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [hCA, hX2, hC2] at h
  have h2 : (2 : ℂ⟦X⟧) * (PowerSeries.X * subst (PowerSeries.X ^ (2 : ℕ))
        (d⁄dX ℂ bottcherVelocitySeries))
      = 2 * (d⁄dX ℂ bottcherVelocitySeries - PowerSeries.X) := by
    linear_combination h
  exact mul_left_cancel₀ h20 h2

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- Every Taylor coefficient of the velocity series lies in the prime subfield of `ℂ`. -/
theorem coeff_bottcherVelocitySeries_mem_bot (k : ℕ) :
    PowerSeries.coeff k bottcherVelocitySeries ∈ (⊥ : Subfield ℂ) := by
  by_cases hp : ∃ m : ℕ, k = 2 ^ (m + 1)
  · obtain ⟨m, rfl⟩ := hp
    rw [coeff_bottcherVelocitySeries_pow m]
    exact inv_mem (natCast_mem (⊥ : Subfield ℂ) _)
  · rw [coeff_bottcherVelocitySeries_of_ne k (fun m hm => hp ⟨m, hm⟩)]
    exact zero_mem _

/-- **Mahler normalization for the Böttcher velocity**: any nonzero formal algebraic
differential equation satisfied by the velocity series over `ℂ` is satisfied with all
coefficients in the prime subfield — the integrality input of any coefficient-isolation
argument on this object. -/
theorem bottcherVelocity_formalADE_descends {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0)
    (hann : MvPolynomial.aeval (formalJets n bottcherVelocitySeries) P = 0) :
    ∃ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 ∧
      (∀ m, MvPolynomial.coeff m Q ∈ (⊥ : Subfield ℂ)) ∧
      MvPolynomial.aeval (formalJets n bottcherVelocitySeries) Q = 0 :=
  formal_mahler_descent coeff_bottcherVelocitySeries_mem_bot hP hann

end GaloisForLFunctions

namespace GaloisForLFunctions

open Classical in
/-- The derivative of the velocity series is the lacunary `0/1` series `∑_j X^{2^{j+1}−1}`:
coefficient `1` exactly at the predecessors of the dyadic powers. -/
theorem coeff_deriv_bottcherVelocitySeries (k : ℕ) :
    PowerSeries.coeff k (d⁄dX ℂ bottcherVelocitySeries)
      = if ∃ m : ℕ, k + 1 = 2 ^ (m + 1) then 1 else 0 := by
  rw [PowerSeries.coeff_derivative]
  by_cases hp : ∃ m : ℕ, k + 1 = 2 ^ (m + 1)
  · obtain ⟨m, hm⟩ := hp
    rw [hm, coeff_bottcherVelocitySeries_pow m, if_pos ⟨m, rfl⟩]
    have hne : ((2 ^ (m + 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
    have hcast : ((k : ℂ) + 1) = ((2 ^ (m + 1) : ℕ) : ℂ) := by
      push_cast [← hm]
      ring
    rw [hcast, inv_mul_cancel₀ hne]
  · rw [coeff_bottcherVelocitySeries_of_ne (k + 1) (fun m hm => hp ⟨m, hm⟩), if_neg hp,
      zero_mul]

/-- **The derivative of the velocity series is irrational**: its support consists of the
predecessors of the dyadic powers, whose gaps double. -/
theorem deriv_bottcherVelocitySeries_not_rational (p q : Polynomial ℂ) (hq : q ≠ 0) :
    (q : ℂ⟦X⟧) * d⁄dX ℂ bottcherVelocitySeries ≠ (p : ℂ⟦X⟧) := by
  refine powerSeries_not_rational_of_gaps (fun g M => ?_) p q hq
  refine ⟨2 ^ (max g M + 1) - 1, ?_, ?_, ?_⟩
  · have h1 : M ≤ max g M := le_max_right _ _
    have h2 : max g M < 2 ^ max g M := Nat.lt_two_pow_self
    have h3 : 2 ^ max g M ≤ 2 ^ (max g M + 1) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
    omega
  · rw [coeff_deriv_bottcherVelocitySeries,
      if_pos ⟨max g M, by
        have h2 : 1 ≤ 2 ^ (max g M + 1) := Nat.one_le_two_pow
        omega⟩]
    exact one_ne_zero
  · intro k hk1 hk2
    rw [coeff_deriv_bottcherVelocitySeries]
    rw [if_neg]
    rintro ⟨m, hm⟩
    have h1le : 1 ≤ 2 ^ (max g M + 1) := Nat.one_le_two_pow
    have hplt : 2 ^ (m + 1) < 2 ^ (max g M + 1) := by omega
    have hlt : m + 1 < max g M + 1 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hplt
    have hle : 2 ^ (m + 1) ≤ 2 ^ max g M :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hg : g < 2 ^ max g M :=
      lt_of_le_of_lt (le_max_left g M) Nat.lt_two_pow_self
    have hpow : 2 ^ (max g M + 1) = 2 * 2 ^ max g M := by ring
    omega

end GaloisForLFunctions
