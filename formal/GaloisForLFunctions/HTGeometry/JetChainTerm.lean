import GaloisForLFunctions.HTGeometry.JetShiftPropagation

/-!
# The terms of the descent chain

Each correction term of the descent chain is a product `V_u·z_k` of a level-free tower entry with a
weight-zero coordinate.  Multiplying the two relations

`R'^{u+2}·Φ(V_u) = R'·V_u + Ê_u`,   `R'^k·Φ(z_k) = R'·z_k + s_k`

gives the relation such a term satisfies, with inhomogeneous term

`Δ(u,k) = V_u·s_k + Ê_u·z_k + Ê_u·s_k/R'`,

and the subdiagonal law computes its descent in any coordinate above the jet orders of `V_u` and
`Ê_u` and different from `k`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- The inhomogeneous term contributed by one chain correction. -/
def chainDelta (R : RatFunc C) (u k : ℕ) : JetField C Unit :=
  invTower (C := C) u * substitutionShiftRatio R k
    + invTowerDefect R u * (jetRatio k : JetField C Unit)
    + invTowerDefect R u * substitutionShiftRatio R k / substitutionDeriv R

/-- **The relation satisfied by one chain correction.** -/
theorem jetSubstitution_invTower_mul (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (u k : ℕ) :
    substitutionDeriv R ^ (u + 1 + k)
        * jetSubstitution R hR (invTower (C := C) u * (jetRatio k : JetField C Unit))
      = substitutionDeriv R * (invTower (C := C) u * (jetRatio k : JetField C Unit))
        + chainDelta R u k := by
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hV := jetSubstitution_invTower R hR u
  have hz := jetSubstitution_jetRatio R hR k
  have hprod : substitutionDeriv R ^ (u + 2 + k)
      * (jetSubstitution R hR (invTower (C := C) u)
        * jetSubstitution R hR (jetRatio k : JetField C Unit))
      = (substitutionDeriv R * invTower (C := C) u + invTowerDefect R u)
        * (substitutionDeriv R * (jetRatio k : JetField C Unit)
          + substitutionShiftRatio R k) := by
    have hsplit : substitutionDeriv R ^ (u + 2 + k)
        = substitutionDeriv R ^ (u + 2) * substitutionDeriv R ^ k := by
      rw [← pow_add]
    rw [hsplit]
    calc substitutionDeriv R ^ (u + 2) * substitutionDeriv R ^ k
          * (jetSubstitution R hR (invTower (C := C) u)
            * jetSubstitution R hR (jetRatio k : JetField C Unit))
        = (substitutionDeriv R ^ (u + 2) * jetSubstitution R hR (invTower (C := C) u))
          * (substitutionDeriv R ^ k
            * jetSubstitution R hR (jetRatio k : JetField C Unit)) := by ring
      _ = _ := by rw [hV, hz]
  rw [map_mul, chainDelta]
  refine mul_left_cancel₀ hρ0 ?_
  have hpow : substitutionDeriv R * substitutionDeriv R ^ (u + 1 + k)
      = substitutionDeriv R ^ (u + 2 + k) := by
    rw [← pow_succ']
    congr 1
    omega
  have hdiv : substitutionDeriv R * (invTowerDefect R u * substitutionShiftRatio R k
      / substitutionDeriv R) = invTowerDefect R u * substitutionShiftRatio R k := by
    field_simp
  linear_combination (jetSubstitution R hR (invTower (C := C) u)
      * jetSubstitution R hR (jetRatio k : JetField C Unit)) * hpow
    + hprod - hdiv

/-- **The descent of one chain correction.** -/
theorem topDescent_chainDelta (R : RatFunc C) {u k K : ℕ} (hK : 2 ≤ K)
    (hVu : topDescent K (invTower (C := C) u) = 0)
    (hEu : topDescent K (invTowerDefect R u) = 0) (hne : K ≠ k) :
    topDescent K (chainDelta R u k)
      = (invTower (C := C) u + invTowerDefect R u / substitutionDeriv R)
        * (((k.choose K : ℕ)) : JetField C Unit) * shiftTower R (k - K) := by
  have hρpd : JetField.pd ((), K) (substitutionDeriv R) = 0 :=
    pd_substitutionDeriv_eq_zero R (by omega)
  have hs := topDescent_substitutionShiftRatio_choose R hK k
  rw [chainDelta, topDescent_add, topDescent_add, topDescent_mul, topDescent_mul,
    topDescent_div_right hρpd, topDescent_mul, hVu, hEu,
    topDescent_jetRatio (show K ≠ 1 by omega), if_neg hne, hs]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
