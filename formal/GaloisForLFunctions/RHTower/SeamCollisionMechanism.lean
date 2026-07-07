/-
# The signature-collision mechanism: an off-line zero is a resolved Krein collision

The seam Krein index counts off-line zeros (`SeamInertiaCharge`), but a count is not a mechanism.
Krein–Gelfand–Lidskii stability theory supplies the missing "how": in a Hamiltonian/Krein setting an
eigenvalue leaves the real axis *only* through a collision of two modes of **opposite Krein
signature**, at which the form degenerates.  This file transposes that mechanism to the functional
equation of `ξ`, and finds it algebraically exact.

The FE conjugate pair `{t, t̄}` builds two carrier vectors on nodes `z`:
`w = e + a` (`a_j = (t−z_j)⁻¹`, `e_j = (t̄−z_j)⁻¹`) and `u = e − a`.  In the factored seam Krein form
`Σ w w* − Σ u u*`, `w` carries the positive square and `u` carries the negative square.  The **order
parameter of the collision is `u`**:

* `seamU_eq_zero_iff_online` — `u = 0` **iff** the pair is on the critical line (`Im t = 0`, where
  `t = t̄` so `e = a`).  The negative carrier vanishes exactly at the collision point.
* `kreinNonneg_of_online` — on the line (`u = 0`) the seam form is `Σ w w*`, positive semidefinite: a
  **definite** form whose positive polarization is *explicitly* the `w` carriers.  Collision
  unresolved ⟹ no negative direction.
* `offLine_opposite_signature` — off the line the carrier is indefinite: it has a strictly positive
  Krein direction *and* a strictly negative one (`conj_pair_carrier_indefinite`).  The two modes of
  opposite signature have separated — the collision has **resolved** into an off-line zero.
* `collision_at_critical_line` — through `t = (ρ−½)·(−i)`, the order parameter vanishes iff `Re ρ = ½`.
  RH is the statement that every FE pair sits exactly at its collision point on the critical line.

So the birth of the negative Krein mode is not a bookkeeping increment but the resolution of a
signature collision: `u` grows from `0` precisely as the pair leaves the line.  The critical line is
the collision locus of the FE-forced Krein form.
-/
import GaloisForLFunctions.RHTower.SeamInertiaCharge
import GaloisForLFunctions.CarrierPickKernel

open Complex Matrix GaloisForLFunctions
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-! ### The collision order parameter -/

/-- **The negative carrier vanishes exactly on the line, node by node.**  `seamU t z i j = 0` iff
`t̄ᵢ = tᵢ`, i.e. `Im tᵢ = 0`: at the collision the two poles `t, t̄` coincide so `e = a` and `u = e−a`
vanishes.  Unconditional (`inv_inj` needs no node-avoidance hypothesis). -/
theorem seamU_apply_eq_zero_iff {k N : ℕ} (t : Fin k → ℂ) (z : Fin N → ℂ) (i : Fin k) (j : Fin N) :
    seamU t z i j = 0 ↔ (t i).im = 0 := by
  unfold seamU
  rw [sub_eq_zero, _root_.inv_inj, sub_left_inj,
    show star (t i) = (starRingEnd ℂ) (t i) from rfl, Complex.conj_eq_iff_im]

/-- **The collision order parameter.**  The negative Krein carrier `u_i = e_i − a_i` of the FE pair
vanishes as a whole vector **iff** the pair is on the critical line (`Im tᵢ = 0`).  Off the line it is
nonzero — the negative mode is present. -/
theorem seamU_eq_zero_iff_online {k N : ℕ} [Nonempty (Fin N)] (t : Fin k → ℂ) (z : Fin N → ℂ)
    (i : Fin k) : seamU t z i = 0 ↔ (t i).im = 0 := by
  constructor
  · intro h
    obtain ⟨j⟩ := (inferInstance : Nonempty (Fin N))
    exact (seamU_apply_eq_zero_iff t z i j).mp (congrFun h j)
  · intro h; funext j; exact (seamU_apply_eq_zero_iff t z i j).mpr h

/-! ### Collision unresolved (on the line) ⟹ definite, with explicit polarization -/

/-- A positive-semidefinite Hermitian Gram has no negative Krein direction. -/
theorem kreinNonneg_of_posSemidef {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.PosSemidef) :
    KreinNonneg H := by
  intro x
  have h := hH.dotProduct_mulVec_nonneg x
  rw [Complex.le_def] at h
  simpa using h.1

/-- With the negative carrier absent (`u = 0`) the factored Krein form is the sum of positive
outer products `Σ w w*`, hence positive semidefinite: the positive polarization is the `w` carriers. -/
theorem factoredKrein_zero_u_posSemidef {N k : ℕ} (w : Fin k → (Fin N → ℂ)) :
    (factoredKreinForm w (0 : Fin k → (Fin N → ℂ))).PosSemidef := by
  have hzero : (∑ i, Matrix.of (fun p q => (0 : Fin k → (Fin N → ℂ)) i p *
      star ((0 : Fin k → (Fin N → ℂ)) i q))) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_); ext p q; simp
  rw [factoredKreinForm, hzero, sub_zero]
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => outer_posSemidef _)

/-- **Collision unresolved ⟹ definite (explicit polarization).**  If every FE pair sits on the
critical line (`Im tᵢ = 0` for all `i`), the seam Krein form has no negative direction
(`KreinNonneg`): the negative carriers all vanish, the form is `Σ w w*`, and its positive polarization
is the FE carriers themselves.  No off-line zero, no signature collision. -/
theorem kreinNonneg_of_online {k N : ℕ} [Nonempty (Fin N)] (t : Fin k → ℂ) (z : Fin N → ℂ)
    (hon : ∀ i, (t i).im = 0) :
    KreinNonneg (factoredKreinForm (seamW t z) (seamU t z)) := by
  have hu : seamU t z = 0 := by
    funext i; exact (seamU_eq_zero_iff_online t z i).mpr (hon i)
  rw [hu]
  exact kreinNonneg_of_posSemidef (factoredKrein_zero_u_posSemidef (seamW t z))

/-- **The modes merge at the collision.**  On the critical line (`Im tᵢ = 0`, so `t̄ᵢ = tᵢ`) the
positive carrier collapses to `w = 2a` (twice the single real-pole resolvent) and the negative carrier
vanishes `u = 0`: the two-dimensional hyperbolic plane `span{w, u}` of opposite Krein signatures
degenerates onto the single positive line `ℂ·a`.  This is the collision made literal — the negative
Krein eigendirection becoming parallel to the positive and annihilating. -/
theorem carrier_merge_online {k N : ℕ} (t : Fin k → ℂ) (z : Fin N → ℂ) (i : Fin k)
    (hon : (t i).im = 0) :
    seamW t z i = (fun j => 2 * (t i - z j)⁻¹) ∧ seamU t z i = 0 := by
  have hst : star (t i) = t i := by
    rw [show star (t i) = (starRingEnd ℂ) (t i) from rfl, Complex.conj_eq_iff_im, hon]
  refine ⟨?_, ?_⟩
  · funext j; simp only [seamW, hst]; ring
  · funext j; simp only [seamU, hst, Pi.zero_apply, sub_self]

/-! ### Collision resolved (off the line) ⟹ opposite Krein signatures -/

/-- **Collision resolved ⟹ opposite signatures.**  For an off-line pair with `Im tᵢ > 0` the negative
carrier is nonzero and the FE carrier is *indefinite*: there is a test point in `ℂ⁺` where the carrier
`m(z) = (tᵢ−z)⁻¹ + (t̄ᵢ−z)⁻¹` has strictly positive imaginary part (a positive Krein direction) and
another where it is strictly negative (a negative Krein direction).  The two modes of opposite Krein
signature have separated: the collision has resolved into an off-line zero. -/
theorem offLine_opposite_signature {k N : ℕ} [Nonempty (Fin N)] (t : Fin k → ℂ) (z : Fin N → ℂ)
    (i : Fin k) (ht : 0 < (t i).im) :
    seamU t z i ≠ 0 ∧
      (∃ w : ℂ, 0 < w.im ∧ 0 < ((t i - w)⁻¹ + (star (t i) - w)⁻¹).im) ∧
      (∃ w : ℂ, 0 < w.im ∧ ((t i - w)⁻¹ + (star (t i) - w)⁻¹).im < 0) := by
  refine ⟨?_, conj_pair_carrier_indefinite (t i) ht⟩
  exact fun h => ht.ne' ((seamU_eq_zero_iff_online t z i).mp h)

/-! ### The seam readoff: the collision locus is the critical line -/

/-- **The collision locus is the critical line.**  Through the descent coordinate
`t = (ρ − ½)·(−i)` (whose imaginary part is `½ − Re ρ`), the collision order parameter vanishes iff
`Re ρ = ½`: the FE pair of a right-half `ξ`-zero `ρ` is at its collision point exactly when `ρ` lies
on the critical line.  RH is the statement that every pair sits at its collision. -/
theorem collision_at_critical_line {N : ℕ} [Nonempty (Fin N)] (ρ : ℂ) (z : Fin N → ℂ) :
    seamU (fun _ : Fin 1 => (ρ - 1 / 2) * (-I)) z 0 = 0 ↔ ρ.re = 1 / 2 := by
  rw [seamU_eq_zero_iff_online]
  have himt : ((ρ - 1 / 2) * (-I)).im = 1 / 2 - ρ.re := by
    simp [Complex.mul_im, Complex.sub_im, Complex.sub_re]
  rw [himt]
  constructor <;> intro h <;> linarith

/-! ### The mechanism, packaged -/

/-- **The signature-collision mechanism.**  For the FE conjugate pair at `tᵢ`:
the negative Krein carrier `uᵢ` is the order parameter — it vanishes iff the pair is on the critical
line; on the line the seam form is definite with explicit positive polarization; off the line (a pair
in `ℂ⁺`) it is indefinite, a positive and a negative Krein direction of opposite signature having
separated.  The off-line zero *is* the resolved signature collision, and `uᵢ` grows from `0` precisely
as the pair leaves the line. -/
theorem collision_mechanism {k N : ℕ} [Nonempty (Fin N)] (t : Fin k → ℂ) (z : Fin N → ℂ) (i : Fin k) :
    (seamU t z i = 0 ↔ (t i).im = 0)
    ∧ ((∀ i', (t i').im = 0) → KreinNonneg (factoredKreinForm (seamW t z) (seamU t z)))
    ∧ (0 < (t i).im → seamU t z i ≠ 0 ∧
        (∃ w : ℂ, 0 < w.im ∧ 0 < ((t i - w)⁻¹ + (star (t i) - w)⁻¹).im) ∧
        (∃ w : ℂ, 0 < w.im ∧ ((t i - w)⁻¹ + (star (t i) - w)⁻¹).im < 0)) :=
  ⟨seamU_eq_zero_iff_online t z i, kreinNonneg_of_online t z,
    offLine_opposite_signature t z i⟩

end

end RHTower
