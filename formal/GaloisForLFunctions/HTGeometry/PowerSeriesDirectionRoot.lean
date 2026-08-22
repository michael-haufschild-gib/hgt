import GaloisForLFunctions.HTGeometry.DirectionEdgeSwaps
import GaloisForLFunctions.HTGeometry.DirectionRadicalField

/-!
# The direction roots as power series

The roots of a single-direction characteristic polynomial are `(s ± ρ)/2`, and the radical `ρ` is a
power series in the transverse coupling.  Realizing the roots themselves as power series — rather
than only inside the Laurent series field where the halving is available — is what identifies them
with the canonical labelled family, whose labels are read off at zero coupling.

## Main results

* `psQuadRoot`, `psCubeQuadRoot`, `psDirectionRoot` — the roots as power series.
* `map_psDirectionRoot` — their images in any field are the field-level roots.
* `constantCoeff_psDirectionRoot` — at zero coupling the root is the diagonal energy of its label.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type} [Field A] {ι : Type}

/-- One endpoint of a hypercube edge in a given direction. -/
def cubeSide {R : Type*} {m : ℕ} (d : (Fin (m + 1) → Bool) → R) (i : Fin (m + 1)) (b : Bool)
    (z : Fin m → Bool) : R :=
  d ((cubeRelabel (Equiv.swap 0 i)).symm (Fin.cons b z))

theorem cubeSide_comp {R S : Type*} {m : ℕ} (f : R → S) (d : (Fin (m + 1) → Bool) → R)
    (i : Fin (m + 1)) (b : Bool) (z : Fin m → Bool) :
    cubeSide (fun x => f (d x)) i b z = f (cubeSide d i b z) := rfl

/-- The two roots of a block quadratic, as power series. -/
def psQuadRoot (s : ι → A) (ρ : ι → PowerSeries A) (p : ι × Bool) : PowerSeries A :=
  PowerSeries.C (2⁻¹ : A) * (PowerSeries.C (s p.1) + (if p.2 then ρ p.1 else -ρ p.1))

theorem constantCoeff_psQuadRoot (s : ι → A) (ρ : ι → PowerSeries A) (p : ι × Bool) :
    PowerSeries.constantCoeff (psQuadRoot s ρ p)
      = 2⁻¹ * (s p.1 + (if p.2 then PowerSeries.constantCoeff (ρ p.1)
          else -PowerSeries.constantCoeff (ρ p.1))) := by
  rw [psQuadRoot, map_mul, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C]
  cases p.2 <;> simp

theorem map_C_inv_two {K : Type*} [Field K] (φ : PowerSeries A →+* K) (h2 : (2 : A) ≠ 0) :
    φ (PowerSeries.C (2⁻¹ : A)) = (2 : K)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h : φ (PowerSeries.C (2⁻¹ : A)) * (2 : K) = φ (PowerSeries.C (2⁻¹ : A) * 2) := by
    rw [map_mul, map_ofNat]
  rw [h, show (2 : PowerSeries A) = PowerSeries.C (2 : A) from (map_ofNat _ 2).symm, ← map_mul,
    inv_mul_cancel₀ h2, map_one, map_one]

theorem map_psQuadRoot {K : Type*} [Field K] (φ : PowerSeries A →+* K) (h2 : (2 : A) ≠ 0)
    (s : ι → A) (ρ : ι → PowerSeries A) (p : ι × Bool) :
    φ (psQuadRoot s ρ p)
      = quadRoot (fun z => φ (PowerSeries.C (s z))) (fun z => φ (ρ z)) p := by
  rw [psQuadRoot, map_mul, map_C_inv_two φ h2, map_add, quadRoot, div_eq_inv_mul]
  congr 1
  cases p.2 <;> simp

variable {m : ℕ}

/-- The block roots labelled by hypercube points, as power series. -/
def psCubeQuadRoot (s : (Fin m → Bool) → A) (ρ : (Fin m → Bool) → PowerSeries A)
    (x : Fin (m + 1) → Bool) : PowerSeries A :=
  psQuadRoot s ρ ((cubePairEquiv m).symm x)

/-- The root family of a single-direction Hamiltonian, as power series. -/
def psDirectionRoot (s : (Fin m → Bool) → A) (ρ : (Fin m → Bool) → PowerSeries A)
    (i : Fin (m + 1)) (x : Fin (m + 1) → Bool) : PowerSeries A :=
  psCubeQuadRoot s ρ (cubeRelabel (Equiv.swap 0 i) x)

theorem map_psDirectionRoot {K : Type*} [Field K] (φ : PowerSeries A →+* K) (h2 : (2 : A) ≠ 0)
    (s : (Fin m → Bool) → A) (ρ : (Fin m → Bool) → PowerSeries A)
    (i : Fin (m + 1)) (x : Fin (m + 1) → Bool) :
    φ (psDirectionRoot s ρ i x)
      = directionRoot (fun z => φ (PowerSeries.C (s z))) (fun z => φ (ρ z)) i x := by
  rw [psDirectionRoot, psCubeQuadRoot, map_psQuadRoot φ h2, directionRoot, cubeQuadRoot]

/-- **At zero coupling the root of a hypercube point is its diagonal energy.** -/
theorem constantCoeff_psDirectionRoot (h2 : (2 : A) ≠ 0) (d : (Fin (m + 1) → Bool) → A)
    (s : (Fin m → Bool) → A) (ρ : (Fin m → Bool) → PowerSeries A) (i : Fin (m + 1))
    (hs : ∀ z, s z = cubeSide d i false z + cubeSide d i true z)
    (hρ : ∀ z, PowerSeries.constantCoeff (ρ z) = cubeSide d i true z - cubeSide d i false z)
    (x : Fin (m + 1) → Bool) :
    PowerSeries.constantCoeff (psDirectionRoot s ρ i x) = d x := by
  classical
  set y : Fin (m + 1) → Bool := cubeRelabel (Equiv.swap 0 i) x with hy
  set z : Fin m → Bool := Fin.tail y with hz
  set b : Bool := y 0 with hb
  have hcons : Fin.cons b z = y := Fin.cons_self_tail y
  have hpair : (cubePairEquiv m).symm y = (z, b) := by
    rw [← hcons]
    exact (cubePairEquiv m).symm_apply_apply (z, b)
  have hx : d x = cubeSide d i b z := by
    rw [cubeSide, hcons, hy, Equiv.symm_apply_apply]
  rw [psDirectionRoot, psCubeQuadRoot, ← hy, hpair, constantCoeff_psQuadRoot, hs, hρ, hx]
  by_cases hbv : b = true
  · rw [hbv, if_pos rfl]
    field_simp
    ring
  · have hbf : b = false := by simpa using hbv
    rw [hbf, if_neg (by exact Bool.false_ne_true)]
    field_simp
    ring


/-- A field map carries the block roots to the block roots of the transported data. -/
theorem map_quadRoot' {K L : Type*} [Field K] [Field L] {F : Type*} [FunLike F K L]
    [RingHomClass F K L] (φ : F) (s ρ : ι → K) (p : ι × Bool) :
    φ (quadRoot s ρ p) = quadRoot (fun z => φ (s z)) (fun z => φ (ρ z)) p := by
  rw [quadRoot, quadRoot, map_div₀, map_add, map_ofNat]
  congr 1
  cases p.2 <;> simp

theorem map_directionRoot {K L : Type*} [Field K] [Field L] {F : Type*} [FunLike F K L]
    [RingHomClass F K L] (φ : F)
    (s ρ : (Fin m → Bool) → K) (i : Fin (m + 1)) (x : Fin (m + 1) → Bool) :
    φ (directionRoot s ρ i x) = directionRoot (fun z => φ (s z)) (fun z => φ (ρ z)) i x := by
  rw [directionRoot, cubeQuadRoot, map_quadRoot', directionRoot, cubeQuadRoot]

end

end GaloisForLFunctions.HTGeometry
