import GaloisForLFunctions.HTGeometry.JetUniformStrip
import GaloisForLFunctions.HTGeometry.JetShiftSecondCoefficient

/-!
# The stage-one coefficient of a normalizing shift

The descent of the defect left by stripping the top coordinate is computed by the subsubtop partial
of the shift:

`topDescent_{N−1}(defect) = ½N(N+1)·(−R''·z₂ + R''' − 2(R'')²/R')`.

That inhomogeneous term is solved by `−½N(N+1)·(z₃ − 2z₂²)`, and eigen-rigidity makes the solution
unique.  So the second coefficient of a normalizing shift is pinned as well, again with no dependence
on the level beyond the scalar `½N(N+1)`; in terms of the Schwarzian it reads
`½N(N+1)·(½z₂² − 𝔖)`, whose jet order is exactly three.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-! ## Calculus of the descent operator -/

omit [CharZero C] in
theorem topDescent_add (N : ℕ) (a b : JetField C Unit) :
    topDescent N (a + b) = topDescent N a + topDescent N b := by
  rw [topDescent, topDescent, topDescent, map_add]
  ring

omit [CharZero C] in
theorem topDescent_sub (N : ℕ) (a b : JetField C Unit) :
    topDescent N (a - b) = topDescent N a - topDescent N b := by
  rw [topDescent, topDescent, topDescent, map_sub]
  ring

omit [CharZero C] in
theorem topDescent_eq_zero {N : ℕ} {a : JetField C Unit} (ha : JetField.pd ((), N) a = 0) :
    topDescent N a = 0 := by
  rw [topDescent, ha, mul_zero]

omit [CharZero C] in
theorem topDescent_mul_left {N : ℕ} {a b : JetField C Unit} (ha : JetField.pd ((), N) a = 0) :
    topDescent N (a * b) = a * topDescent N b := by
  have hleib := (JetField.pd ((), N) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz a b
  simp only [smul_eq_mul] at hleib
  rw [topDescent, topDescent, hleib, ha, mul_zero, add_zero]
  ring

omit [CharZero C] in
theorem topDescent_mul_right {N : ℕ} {a b : JetField C Unit} (hb : JetField.pd ((), N) b = 0) :
    topDescent N (a * b) = topDescent N a * b := by
  rw [mul_comm, topDescent_mul_left hb]
  ring

omit [CharZero C] in
theorem pd_inv_eq_zero {j : ℕ} {a : JetField C Unit} (ha : JetField.pd ((), j) a = 0) :
    JetField.pd ((), j) a⁻¹ = 0 := by
  have h := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz_inv a
  rw [h, ha]
  simp

omit [CharZero C] in
theorem pd_div_eq_zero {j : ℕ} {a b : JetField C Unit} (ha : JetField.pd ((), j) a = 0)
    (hb : JetField.pd ((), j) b = 0) : JetField.pd ((), j) (a / b) = 0 := by
  have hleib := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz a b⁻¹
  simp only [smul_eq_mul] at hleib
  rw [div_eq_mul_inv, hleib, ha, pd_inv_eq_zero hb, mul_zero, mul_zero, add_zero]

omit [CharZero C] in
theorem pd_natCast_eq_zero (j n : ℕ) :
    JetField.pd ((), j) ((n : ℕ) : JetField C Unit) = 0 := by
  rw [show ((n : ℕ) : JetField C Unit) = algebraMap C (JetField C Unit) ((n : ℕ) : C) from
    (map_natCast (algebraMap C (JetField C Unit)) n).symm, Derivation.map_algebraMap]

omit [CharZero C] in
theorem topDescent_div_right {N : ℕ} {a b : JetField C Unit} (hb : JetField.pd ((), N) b = 0) :
    topDescent N (a / b) = topDescent N a / b := by
  rw [div_eq_mul_inv, topDescent_mul_right (pd_inv_eq_zero hb), div_eq_mul_inv]

/-! ## The descent of the defect -/

theorem topDescent_substitutionShiftRatio_two_up (R : RatFunc C) {N : ℕ} (hN : 4 ≤ N) :
    topDescent (N - 1) (substitutionShiftRatio R (N + 1))
      = ((N * (N + 1) : ℕ) : JetField C Unit)
        * (JetField.pd ((), 0) (substitutionDeriv R) * (jetRatio 2 : JetField C Unit)
          + JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R)))
        / 2 := by
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 4 := ⟨N - 4, by omega⟩
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hidx : K + 4 - 1 = K + 3 := by omega
  rw [hidx]
  have hsec := pd_second_substitutionShift_eq R (K + 2)
  have hshape : K + 2 + 3 = K + 4 + 1 := by omega
  have hshape2 : K + 2 + 1 = K + 3 := by omega
  rw [hshape, hshape2] at hsec
  -- pass to the weight-zero shift
  have hmul : substitutionShiftRatio R (K + 4 + 1)
      * (JetField.jet ((), 1) : JetField C Unit) ^ (K + 4 + 1)
      = substitutionShift R (K + 4 + 1) := by
    rw [substitutionShiftRatio]
    field_simp
  have hpow : JetField.pd ((), K + 3)
      ((JetField.jet ((), 1) : JetField C Unit) ^ (K + 4 + 1)) = 0 := by
    have hl := (JetField.pd ((), K + 3) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
        (JetField.jet ((), 1) : JetField C Unit) (K + 4 + 1)
    rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
    simpa using hl
  have hleib := (JetField.pd ((), K + 3) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionShiftRatio R (K + 4 + 1))
      ((JetField.jet ((), 1) : JetField C Unit) ^ (K + 4 + 1))
  simp only [smul_eq_mul] at hleib
  rw [hmul, hpow, mul_zero, zero_add] at hleib
  -- read off the descent
  rw [topDescent]
  have hz2 : (jetRatio 2 : JetField C Unit)
      = (JetField.jet ((), 2) : JetField C Unit)
        / (JetField.jet ((), 1) : JetField C Unit) ^ 2 := rfl
  have hcoef : ((K + 2 + 2) * (K + 2 + 3) : ℕ) = ((K + 4) * (K + 4 + 1) : ℕ) := by ring
  rw [hcoef] at hsec
  rw [hz2]
  refine mul_left_cancel₀ (show (2 : JetField C Unit) ≠ 0 from two_ne_zero) ?_
  refine mul_right_cancel₀ (pow_ne_zero (K + 4 + 1) hy1) ?_
  field_simp
  linear_combination hsec - 2 * hleib

omit [CharZero C] in
theorem pd_mul_eq_zero {j : ℕ} {a b : JetField C Unit} (ha : JetField.pd ((), j) a = 0)
    (hb : JetField.pd ((), j) b = 0) : JetField.pd ((), j) (a * b) = 0 := by
  have hleib := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz a b
  simp only [smul_eq_mul] at hleib
  rw [hleib, ha, hb, mul_zero, mul_zero, add_zero]

omit [CharZero C] in
theorem pd_pow_eq_zero {j : ℕ} {a : JetField C Unit} (ha : JetField.pd ((), j) a = 0) (n : ℕ) :
    JetField.pd ((), j) (a ^ n) = 0 := by
  have hl := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow a n
  rw [ha] at hl
  simpa using hl

/-! ## The stage-one defect and its solution -/

/-- The inhomogeneous term of the stage-one relation. -/
def zshiftDefectOne (R : RatFunc C) (N : ℕ) : JetField C Unit :=
  ((N * (N + 1) : ℕ) : JetField C Unit)
      * (JetField.pd ((), 0) (substitutionDeriv R) * (jetRatio 2 : JetField C Unit)
        + JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R))) / 2
    - ((N * (N + 1) : ℕ) : JetField C Unit)
      * (JetField.pd ((), 0) (substitutionDeriv R) * (jetRatio 2 : JetField C Unit)
        + JetField.pd ((), 0) (substitutionDeriv R) ^ 2 / substitutionDeriv R)

/-- **The descent of the defect.** -/
theorem topDescent_zshiftDefect (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ}
    (hN : 4 ≤ N) : topDescent (N - 1) (zshiftDefect R N) = zshiftDefectOne R N := by
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hρ1 : JetField.pd ((), N - 1) (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
    rw [pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
  have hρ : JetField.pd ((), N - 1) (substitutionDeriv R) = 0 :=
    pd_substitutionDeriv_eq_zero R (by omega)
  have hz2 : JetField.pd ((), N - 1) (jetRatio 2 : JetField C Unit) = 0 :=
    pd_jetRatio_of_ne (by omega) (by omega)
  have hzN : JetField.pd ((), N - 1) (jetRatio N : JetField C Unit) = 0 :=
    pd_jetRatio_of_ne (by omega) (by omega)
  have hsN : topDescent (N - 1) (substitutionShiftRatio R N)
      = ((N : ℕ) : JetField C Unit) * JetField.pd ((), 0) (substitutionDeriv R) := by
    have h := topDescent_substitutionShiftRatio R (show 2 ≤ N - 1 by omega)
    rw [show N - 1 + 1 = N from by omega] at h
    exact h
  rw [zshiftDefect, topDescent_sub, topDescent_substitutionShiftRatio_two_up R hN,
    topDescent_div_right hρ, topDescent_mul_left (pd_natCast_eq_zero _ _),
    topDescent_add, topDescent_add,
    topDescent_mul_left (pd_mul_eq_zero hρ hρ1), topDescent_eq_zero hzN,
    topDescent_mul_left (pd_mul_eq_zero hρ hz2), topDescent_mul_left hρ1, hsN, zshiftDefectOne]
  field_simp
  push_cast
  ring

/-- The stage-one coefficient. -/
def zshiftCoeffOne (C : Type*) [Field C] [CharZero C] (N : ℕ) : JetField C Unit :=
  -(((N * (N + 1) : ℕ) : JetField C Unit) / 2)
    * ((jetRatio 3 : JetField C Unit) - 2 * (jetRatio 2 : JetField C Unit) ^ 2)

/-- **The stage-one coefficient solves the stage-one relation.** -/
theorem zshiftCoeffOne_relation (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (N : ℕ) :
    substitutionDeriv R ^ 3 * jetSubstitution R hR (zshiftCoeffOne C N)
      = substitutionDeriv R * zshiftCoeffOne C N - zshiftDefectOne R N := by
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have h2 := jetSubstitution_jetRatio R hR 2
  rw [substitutionShiftRatio_two] at h2
  have h3 := jetSubstitution_jetRatio R hR 3
  rw [substitutionShiftRatio_three] at h3
  have hsq : substitutionDeriv R ^ 4
      * jetSubstitution R hR ((jetRatio 2 : JetField C Unit) ^ 2)
      = (substitutionDeriv R * (jetRatio 2 : JetField C Unit)
        + JetField.pd ((), 0) (substitutionDeriv R)) ^ 2 := by
    rw [map_pow]
    calc substitutionDeriv R ^ 4 * jetSubstitution R hR (jetRatio 2 : JetField C Unit) ^ 2
        = (substitutionDeriv R ^ 2 * jetSubstitution R hR (jetRatio 2 : JetField C Unit)) ^ 2 := by
          ring
      _ = _ := by rw [h2]
  rw [zshiftCoeffOne, zshiftDefectOne, map_mul, map_neg, map_div₀, map_natCast, map_ofNat,
    map_sub, map_mul, map_ofNat]
  field_simp
  linear_combination
    (-(((N * (N + 1) : ℕ) : JetField C Unit)) * substitutionDeriv R) * h3
    + (2 * ((N * (N + 1) : ℕ) : JetField C Unit)) * hsq

/-! ## The pinned stage-one coefficient -/

theorem IsWeightZero.div {a b : JetField C Unit} (ha : IsWeightZero a) (hb : IsWeightZero b) :
    IsWeightZero (a / b) := by
  show weightScale (show (2 : C) ≠ 0 from two_ne_zero) (a / b) = a / b
  rw [map_div₀, show weightScale (show (2 : C) ≠ 0 from two_ne_zero) a = a from ha,
    show weightScale (show (2 : C) ≠ 0 from two_ne_zero) b = b from hb]

theorem IsWeightZero.sub {a b : JetField C Unit} (ha : IsWeightZero a) (hb : IsWeightZero b) :
    IsWeightZero (a - b) := by
  show weightScale (show (2 : C) ≠ 0 from two_ne_zero) (a - b) = a - b
  rw [map_sub, show weightScale (show (2 : C) ≠ 0 from two_ne_zero) a = a from ha,
    show weightScale (show (2 : C) ≠ 0 from two_ne_zero) b = b from hb]

theorem IsWeightZero.pow {a : JetField C Unit} (ha : IsWeightZero a) (n : ℕ) :
    IsWeightZero (a ^ n) := by
  show weightScale (show (2 : C) ≠ 0 from two_ne_zero) (a ^ n) = a ^ n
  rw [map_pow, show weightScale (show (2 : C) ≠ 0 from two_ne_zero) a = a from ha]

theorem isWeightZero_natCast (n : ℕ) : IsWeightZero ((n : ℕ) : JetField C Unit) := by
  show weightScale (show (2 : C) ≠ 0 from two_ne_zero) ((n : ℕ) : JetField C Unit) = _
  rw [map_natCast]

theorem isWeightZero_two : IsWeightZero (2 : JetField C Unit) := by
  have h := isWeightZero_natCast (C := C) 2
  rwa [Nat.cast_ofNat] at h

omit [CharZero C] in
theorem pd_two_eq_zero (j : ℕ) : JetField.pd ((), j) (2 : JetField C Unit) = 0 := by
  rw [show (2 : JetField C Unit) = algebraMap C (JetField C Unit) (2 : C) from
    (map_ofNat (algebraMap C (JetField C Unit)) 2).symm, Derivation.map_algebraMap]

theorem isWeightZero_zshiftCoeffOne (N : ℕ) : IsWeightZero (zshiftCoeffOne C N) := by
  rw [zshiftCoeffOne]
  refine IsWeightZero.mul (IsWeightZero.neg
    ((isWeightZero_natCast _).div isWeightZero_two)) ?_
  exact (isWeightZero_jetRatio 3).sub
    (isWeightZero_two.mul ((isWeightZero_jetRatio 2).pow 2))

theorem pd_zshiftCoeffOne_eq_zero {N j : ℕ} (hN : 4 ≤ N) (hj : N < j) :
    JetField.pd ((), j) (zshiftCoeffOne C N) = 0 := by
  rw [zshiftCoeffOne]
  refine pd_mul_eq_zero ?_ ?_
  · rw [map_neg, pd_div_eq_zero (pd_natCast_eq_zero _ _) (pd_two_eq_zero _), neg_zero]
  · rw [map_sub, pd_jetRatio_of_ne (by omega) (by omega),
      pd_mul_eq_zero (pd_two_eq_zero _) (pd_pow_eq_zero (pd_jetRatio_of_ne (by omega) (by omega)) 2),
      sub_zero]

/-- **The second coefficient of a normalizing shift, at every level above three.**  Stripping the
pinned top term and descending once more gives a relation of exponent three whose unique solution is
`−½N(N+1)·(z₃ − 2z₂²) = ½N(N+1)·(½z₂² − 𝔖)`. -/
theorem topDescent_strip_of_zshift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ}
    (hN : 4 ≤ N)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (hord : ∀ j : ℕ, N < j → JetField.pd ((), j) w = 0)
    (heq : substitutionDeriv R ^ (N + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (N + 1)) :
    topDescent (N - 1) (w + ((N + 1 : ℕ) : JetField C Unit)
        * (jetRatio 2 : JetField C Unit) * (jetRatio N : JetField C Unit))
      = zshiftCoeffOne C N := by
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  obtain ⟨huwz, huord, hueq⟩ := zshift_strip R hR (by omega) hfix hwz hord heq
  set u : JetField C Unit := w + ((N + 1 : ℕ) : JetField C Unit)
    * (jetRatio 2 : JetField C Unit) * (jetRatio N : JetField C Unit) with hudef
  have huordlt : ∀ j : ℕ, N - 1 < j → JetField.pd ((), j) u = 0 := fun j hj =>
    huord j (by omega)
  have hueqZ : substitutionDeriv R ^ (((N + 1 : ℕ)) : ℤ) * jetSubstitution R hR u
      = substitutionDeriv R * u - zshiftDefect R N := by
    rw [zpow_natCast]
    exact hueq
  have hstep := jetSubstitution_topDescent R hR (show 1 ≤ N - 1 by omega) huordlt hueqZ
  have hexp : ((N + 1 : ℕ) : ℤ) + 1 - ((N - 1 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) := by
    have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by
      have h := Nat.cast_sub (R := ℤ) (show 1 ≤ N by omega)
      simpa using h
    rw [hc]
    push_cast
    ring
  rw [hexp, zpow_natCast, topDescent_zshiftDefect R hR hN] at hstep
  -- the difference of the two solutions is a pure eigen-element of exponent two
  set P : JetField C Unit := topDescent (N - 1) u with hPdef
  have hsol := zshiftCoeffOne_relation R hR N
  have hdiff : substitutionDeriv R ^ (2 : ℤ)
      * jetSubstitution R hR (P - zshiftCoeffOne C N) = P - zshiftCoeffOne C N := by
    refine mul_left_cancel₀ hρ0 ?_
    have hz : substitutionDeriv R * substitutionDeriv R ^ (2 : ℤ)
        = substitutionDeriv R ^ (3 : ℕ) := by
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast]
      ring
    rw [← mul_assoc, hz, map_sub, mul_sub]
    rw [hstep, hsol]
    ring
  by_cases hzero : P - zshiftCoeffOne C N = 0
  · exact sub_eq_zero.mp hzero
  · exfalso
    have hwzP : IsWeightZero P := isWeightZero_topDescent huwz
    have hordP : ∀ j : ℕ, N < j → JetField.pd ((), j) (P - zshiftCoeffOne C N) = 0 := by
      intro j hj
      rw [map_sub, pd_zshiftCoeffOne_eq_zero hN hj, sub_zero, hPdef]
      exact topDescent_order (show 1 ≤ N - 1 by omega) huordlt j (by omega)
    have := exponent_eq_zero_of_weightZero_eigen R hR (K := N) (by omega) hfix
      (hwzP.sub (isWeightZero_zshiftCoeffOne N)) hzero hordP hdiff
    exact absurd this (by norm_num)

end

end GaloisForLFunctions.HTGeometry
