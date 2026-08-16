import GaloisForLFunctions.HTGeometry.PhysicalCharacteristicIncidence
import GaloisForLFunctions.HTGeometry.AlternatingContraction

/-!
# The Cartan identity and Koszul contractibility

The Koszul differential of a linear functional `φ` is contraction by `φ`.  Left exterior
multiplication by a vector `e` is its adjoint operation, and the two satisfy the Cartan identity

`ι_φ (e ∧ ω) + e ∧ ι_φ ω = φ(e) · ω`.

When `φ(e)` is invertible the identity is a chain homotopy between the identity and zero, so the
Koszul complex is contractible: a single invertible coordinate contracts the whole complex.

## Main results

* `wedgeLeft` — left exterior multiplication by a vector, between exterior powers;
* `koszul_cartan_succ`, `koszul_cartan_zero_map` — the Cartan identity in every degree;
* `koszul_contraction` — the chain homotopy attached to an invertible coordinate;
* `physicalKoszulDifferential_exact` — exactness of the complex in every degree.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Index bookkeeping -/

theorem removeNth_zero_cons {V : Type*} {k : ℕ} (e : V) (w : Fin k → V) :
    Fin.removeNth (α := fun _ : Fin (k + 1) => V) 0 (Fin.cons e w) = w := by
  funext l
  simp only [Fin.removeNth, Fin.succAbove_zero, Fin.cons_succ]

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Left exterior multiplication by a fixed vector. -/
def wedgeLeft (k : ℕ) (e : V) : (⋀[R]^k V) →ₗ[R] (⋀[R]^(k + 1) V) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.curryLeft (exteriorPower.ιMulti R (k + 1)) e)

@[simp]
theorem wedgeLeft_ιMulti (k : ℕ) (e : V) (v : Fin k → V) :
    wedgeLeft (R := R) k e (exteriorPower.ιMulti R k v)
      = exteriorPower.ιMulti R (k + 1) (Fin.cons e v) := by
  rw [wedgeLeft, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]
  rfl

/-! ### The Cartan identity -/

theorem koszul_cartan_zero (phi : V →ₗ[R] R) (e : V) (v : Fin 0 → V) :
    physicalKoszulDifferential 0 phi (wedgeLeft 0 e (exteriorPower.ιMulti R 0 v))
      = phi e • exteriorPower.ιMulti R 0 v := by
  have hrm : Fin.removeNth (α := fun _ : Fin 1 => V) 0 (Fin.cons e v) = v :=
    Subsingleton.elim _ _
  rw [wedgeLeft_ιMulti, physicalKoszulDifferential_ιMulti, Fin.sum_univ_one, hrm]
  simp

theorem koszul_cartan_succ_ιMulti (m : ℕ) (phi : V →ₗ[R] R) (e : V) (w : Fin (m + 1) → V) :
    physicalKoszulDifferential (m + 1) phi
        (wedgeLeft (m + 1) e (exteriorPower.ιMulti R (m + 1) w))
      + wedgeLeft m e (physicalKoszulDifferential m phi (exteriorPower.ιMulti R (m + 1) w))
      = phi e • exteriorPower.ιMulti R (m + 1) w := by
  rw [wedgeLeft_ιMulti, physicalKoszulDifferential_ιMulti,
    physicalKoszulDifferential_ιMulti, Fin.sum_univ_succ, map_sum, add_assoc,
    ← Finset.sum_add_distrib]
  have hfirst : ((-1 : ℤ) ^ ((0 : Fin (m + 2)) : ℕ)) •
      (phi ((Fin.cons e w : Fin (m + 2) → V) 0) •
        exteriorPower.ιMulti R (m + 1)
          (Fin.removeNth (α := fun _ : Fin (m + 2) => V) 0 (Fin.cons e w)))
      = phi e • exteriorPower.ιMulti R (m + 1) w := by
    rw [removeNth_zero_cons, Fin.cons_zero]
    simp
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
      ((-1 : ℤ) ^ ((j.succ : Fin (m + 2)) : ℕ)) •
          (phi ((Fin.cons e w : Fin (m + 2) → V) j.succ) •
            exteriorPower.ιMulti R (m + 1)
              (Fin.removeNth (α := fun _ : Fin (m + 2) => V) j.succ (Fin.cons e w)))
        + wedgeLeft m e (((-1 : ℤ) ^ ((j : Fin (m + 1)) : ℕ)) •
            (phi (w j) • exteriorPower.ιMulti R m
              (Fin.removeNth (α := fun _ : Fin (m + 1) => V) j w))) = 0 := by
    intro j _
    rw [removeNth_succ_cons, Fin.cons_succ, map_zsmul, map_smul, wedgeLeft_ιMulti,
      Fin.val_succ, ← add_zsmul]
    have hsign : ((-1 : ℤ) ^ ((j : ℕ) + 1) + (-1 : ℤ) ^ ((j : ℕ))) = 0 := by
      rw [pow_succ]; ring
    rw [hsign, zero_zsmul]
  rw [hfirst, Finset.sum_congr rfl hterm, Finset.sum_const_zero, add_zero]

/-- **The Cartan identity.**  Contraction by `φ` and left multiplication by `e` sum to the scalar
`φ(e)` on every exterior power. -/
theorem koszul_cartan_succ (m : ℕ) (phi : V →ₗ[R] R) (e : V) :
    (physicalKoszulDifferential (m + 1) phi).comp (wedgeLeft (m + 1) e)
        + (wedgeLeft m e).comp (physicalKoszulDifferential m phi)
      = phi e • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  exact koszul_cartan_succ_ιMulti m phi e w

theorem koszul_cartan_zero_map (phi : V →ₗ[R] R) (e : V) :
    (physicalKoszulDifferential 0 phi).comp (wedgeLeft 0 e) = phi e • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  exact koszul_cartan_zero phi e w

/-! ### Contractibility from one invertible coordinate -/

/-- **The Koszul contraction.**  If `φ(e)` is invertible, the maps `b • (e ∧ ·)` form a chain
homotopy between the identity and zero. -/
theorem koszul_contraction (m : ℕ) (phi : V →ₗ[R] R) (e : V) {b : R} (hb : b * phi e = 1) :
    (physicalKoszulDifferential (m + 1) phi).comp (b • wedgeLeft (m + 1) e)
        + (b • wedgeLeft m e).comp (physicalKoszulDifferential m phi)
      = LinearMap.id := by
  have hsmul : (physicalKoszulDifferential (m + 1) phi).comp (b • wedgeLeft (m + 1) e)
      + (b • wedgeLeft m e).comp (physicalKoszulDifferential m phi)
      = b • ((physicalKoszulDifferential (m + 1) phi).comp (wedgeLeft (m + 1) e)
        + (wedgeLeft m e).comp (physicalKoszulDifferential m phi)) := by
    ext x
    simp [smul_add]
  rw [hsmul, koszul_cartan_succ m phi e, smul_smul, hb, one_smul]

/-- **Exactness in positive degrees.**  A single invertible coordinate makes the Koszul complex
exact: every cycle is a boundary. -/
theorem physicalKoszulDifferential_exact (m : ℕ) (phi : V →ₗ[R] R) (e : V) {b : R}
    (hb : b * phi e = 1) {x : ⋀[R]^(m + 1) V} (hx : physicalKoszulDifferential m phi x = 0) :
    ∃ y : ⋀[R]^(m + 2) V, physicalKoszulDifferential (m + 1) phi y = x := by
  refine ⟨b • wedgeLeft (m + 1) e x, ?_⟩
  have h := congrArg (fun f : (⋀[R]^(m + 1) V) →ₗ[R] (⋀[R]^(m + 1) V) => f x)
    (koszul_contraction m phi e hb)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.smul_apply] at h
  rw [hx] at h
  simpa using h

/-- **Surjectivity in degree zero.** -/
theorem physicalKoszulDifferential_surjective_zero (phi : V →ₗ[R] R) (e : V) {b : R}
    (hb : b * phi e = 1) (x : ⋀[R]^0 V) :
    ∃ y : ⋀[R]^1 V, physicalKoszulDifferential 0 phi y = x := by
  refine ⟨b • wedgeLeft 0 e x, ?_⟩
  have h := congrArg (fun f : (⋀[R]^0 V) →ₗ[R] (⋀[R]^0 V) => f x) (koszul_cartan_zero_map phi e)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [map_smul, h, smul_smul, hb, one_smul]

end GaloisForLFunctions.HTGeometry
