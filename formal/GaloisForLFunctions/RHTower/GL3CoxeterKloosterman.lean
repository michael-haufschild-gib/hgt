import GaloisForLFunctions.RHTower.GL3CoxeterCell
import GaloisForLFunctions.RHTower.HyperKloostermanRootNumber
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Fin.Basic


/-!
# The `w₃` Kloosterman sum at moduli `(D, D²)` is `D · Kl₃`

For `SL₃(ℤ)` the long-element-free Coxeter cell `w₃` carries Kloosterman sums indexed by pairs of
moduli `(D, A)` with `D ∣ A` (`plk1_dvd`), and the phases are the entries of the explicit Bruhat
decomposition (`w3_bruhat`, `cell_phase1`, `cell_phase2`, `cell_phase_right`). At `A = D²` the orbit
data are `p₀ ∈ (ℤ/D)ˣ` and `C ∈ ℤ/D²` with `C` a unit mod `D`, and the phase depends on `C` only
mod `D`.

* `sum_redSq`: every fibre of `ℤ/D² → ℤ/D` has `D` points.
* `coxeterKloosterman_eq`: `S_{w₃}(m₁, m₂, n₂; D, D²) = D · Σ_{x,z ∈ (ℤ/D)ˣ} ψ(−(m₁x + m₂(xz)⁻¹ + n₂z))`.
* `hyperKloosterman_three_unit`: the corpus `Kl₃(a; D)` as a sum over unit pairs.
* `coxeterKloosterman_eq_hyperKloosterman`: for unit weights,
  `S_{w₃}(m₁, m₂, n₂; D, D²) = D · Kl₃(−m₁m₂n₂; D)`.

This is the identity through which the `GL(3)` Kuznetsov formula for the `w₃` cell sees the
hyper-Kloosterman sum `Kl₃`; the moduli-sum over `D` is the arithmetic side of the Sym²-lift
spectral problem.
-/

open Finset

namespace GaloisForLFunctions.RHTower.GL3

variable {D : ℕ} [NeZero D]

/-- Reduction `ℤ/D² → ℤ/D`. -/
abbrev redSq (D : ℕ) : ZMod (D * D) →+* ZMod D := ZMod.castHom (dvd_mul_right D D) (ZMod D)

omit [NeZero D] in
theorem redSq_surjective : Function.Surjective (redSq D) := ZMod.ringHom_surjective _

/-- **Fibre count.** Every fibre of `ℤ/D² → ℤ/D` has `D` elements, so
`Σ_{C mod D²} g(C mod D) = D · Σ_{c mod D} g(c)`. -/
theorem sum_redSq {M : Type*} [AddCommMonoid M] (g : ZMod D → M) :
    ∑ C : ZMod (D * D), g (redSq D C) = D • ∑ c : ZMod D, g c := by
  classical
  have hfib : ∀ c : ZMod D, #{C : ZMod (D * D) | redSq D C = c} = D := by
    have hall : ∀ c c' : ZMod D, #{C : ZMod (D * D) | redSq D C = c} =
        #{C : ZMod (D * D) | redSq D C = c'} := fun c c' =>
      AddMonoidHom.card_fiber_eq_of_mem_range (redSq D).toAddMonoidHom
        (redSq_surjective c) (redSq_surjective c')
    have htot : ∑ c : ZMod D, #{C : ZMod (D * D) | redSq D C = c} = D * D := by
      rw [← Finset.card_eq_sum_card_fiberwise (f := redSq D) (by simp)]
      simp [ZMod.card]
    intro c
    rw [Finset.sum_congr rfl (fun c' _ => hall c' c), Finset.sum_const, Finset.card_univ,
      ZMod.card, smul_eq_mul] at htot
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne D)) htot
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := redSq D) (f := fun C => g (redSq D C))]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_congr rfl (fun C hC => by rw [(Finset.mem_filter.1 hC).2]), Finset.sum_const,
    hfib c]

/-- The phase of the Coxeter orbit datum `(p₀, c)`: `ψ(−m₁c⁻¹ − m₂p₀⁻¹c − n₂p₀)` for `c` a unit, else `0`. -/
noncomputable def coxPhase (ψ : AddChar (ZMod D) ℂ) (m1 m2 n2 : ZMod D) (p0 : (ZMod D)ˣ)
    (c : ZMod D) : ℂ := by
  classical
  exact if h : IsUnit c then ψ (-(m1 * ↑h.unit⁻¹) - m2 * (↑p0⁻¹ * c) - n2 * ↑p0) else 0

/-- **The `w₃` Kloosterman sum at moduli `(D, D²)`.** It runs over the Coxeter orbit data
`p₀ ∈ (ℤ/D)ˣ`, `C ∈ ℤ/D²` (`C` a unit mod `D`), with the phases of `cell_phase1`, `cell_phase2`,
`cell_phase_right`. -/
noncomputable def coxeterKloosterman (ψ : AddChar (ZMod D) ℂ) (m1 m2 n2 : ZMod D) : ℂ :=
  ∑ p0 : (ZMod D)ˣ, ∑ C : ZMod (D * D), coxPhase ψ m1 m2 n2 p0 (redSq D C)

theorem coxPhase_unit (ψ : AddChar (ZMod D) ℂ) (m1 m2 n2 : ZMod D) (p0 c : (ZMod D)ˣ) :
    coxPhase ψ m1 m2 n2 p0 c = ψ (-(m1 * ↑c⁻¹) - m2 * (↑p0⁻¹ * ↑c) - n2 * ↑p0) := by
  classical
  simp only [coxPhase, dif_pos c.isUnit, IsUnit.unit_of_val_units]

theorem coxPhase_nonunit (ψ : AddChar (ZMod D) ℂ) (m1 m2 n2 : ZMod D) (p0 : (ZMod D)ˣ)
    {c : ZMod D} (hc : ¬ IsUnit c) : coxPhase ψ m1 m2 n2 p0 c = 0 := by
  classical
  simp only [coxPhase, dif_neg hc]

theorem sum_coxPhase_units (ψ : AddChar (ZMod D) ℂ) (m1 m2 n2 : ZMod D) (p0 : (ZMod D)ˣ) :
    ∑ c : ZMod D, coxPhase ψ m1 m2 n2 p0 c =
      ∑ c : (ZMod D)ˣ, ψ (-(m1 * ↑c⁻¹) - m2 * (↑p0⁻¹ * ↑c) - n2 * ↑p0) := by
  classical
  let e : (ZMod D)ˣ ↪ ZMod D := ⟨(↑), Units.val_injective⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun c _ hc => ?_),
    Finset.sum_map]
  · exact Finset.sum_congr rfl fun c _ => coxPhase_unit ψ m1 m2 n2 p0 c
  · apply coxPhase_nonunit
    rintro ⟨u, rfl⟩
    exact hc (Finset.mem_map_of_mem e (Finset.mem_univ u))

/-- **The `w₃` Kloosterman sum is `D` times a hyper-Kloosterman sum.** Substituting `x = C⁻¹`,
`z = p₀` (so `y = p₀⁻¹C = (xz)⁻¹`):
`S_{w₃}(m, n; D, D²) = D · Σ_{x,z ∈ (ℤ/D)ˣ} ψ(−(m₁x + m₂(xz)⁻¹ + n₂z))`. -/
theorem coxeterKloosterman_eq (ψ : AddChar (ZMod D) ℂ) (m1 m2 n2 : ZMod D) :
    coxeterKloosterman ψ m1 m2 n2 =
      D • ∑ x : (ZMod D)ˣ, ∑ z : (ZMod D)ˣ,
        ψ (-(m1 * ↑x + m2 * ↑(x * z)⁻¹ + n2 * ↑z)) := by
  unfold coxeterKloosterman
  simp_rw [sum_redSq (g := coxPhase ψ m1 m2 n2 _), ← Finset.smul_sum, sum_coxPhase_units]
  congr 1
  rw [Finset.sum_comm]
  apply Fintype.sum_equiv (Equiv.inv (ZMod D)ˣ)
  intro c
  apply Finset.sum_congr rfl
  intro p0 _
  congr 1
  simp only [Equiv.inv_apply, inv_inv, mul_inv_rev, Units.val_mul]
  ring

/-! ### Comparison with the hyper-Kloosterman sum `Kl₃` -/

open GaloisForLFunctions.RHTower.HyperKloosterman

/-- Triples as functions on `Fin 3`. -/
def triEquiv (R : Type*) : R × R × R ≃ (Fin 3 → R) where
  toFun t := ![t.1, t.2.1, t.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv t := by simp
  right_inv v := by ext i; fin_cases i <;> rfl

theorem hyperKloosterman_three (ψ : AddChar (ZMod D) ℂ) (a : ZMod D) :
    hyperKloosterman ψ 3 a =
      ∑ u : ZMod D, ∑ w : ZMod D, ∑ v : ZMod D, if u * v * w = a then ψ (u + v + w) else 0 := by
  unfold hyperKloosterman
  rw [← (triEquiv (ZMod D)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  apply Finset.sum_congr rfl; intro v _
  simp [triEquiv, Fin.prod_univ_three, Fin.sum_univ_three]

/-- For a unit `a`, the `v`-sum in `Kl₃(a)` has exactly one term when `u, w` are units and none
otherwise. -/
theorem inner_sum_unit (ψ : AddChar (ZMod D) ℂ) (a : (ZMod D)ˣ) (u w : ZMod D) :
    (∑ v : ZMod D, if u * v * w = (a : ZMod D) then ψ (u + v + w) else 0) =
      if h : IsUnit u ∧ IsUnit w then ψ (u + ↑(a * h.1.unit⁻¹ * h.2.unit⁻¹) + w) else 0 := by
  classical
  split_ifs with h
  · rw [Finset.sum_eq_single (↑(a * h.1.unit⁻¹ * h.2.unit⁻¹))]
    · rw [if_pos]
      simp only [Units.val_mul]
      have hu : u * ↑h.1.unit⁻¹ = 1 := h.1.mul_val_inv
      have hw : ↑h.2.unit⁻¹ * w = 1 := h.2.val_inv_mul
      calc u * (↑a * ↑h.1.unit⁻¹ * ↑h.2.unit⁻¹) * w
          = ↑a * (u * ↑h.1.unit⁻¹) * (↑h.2.unit⁻¹ * w) := by ring
        _ = ↑a := by rw [hu, hw, mul_one, mul_one]
    · intro v _ hv
      rw [if_neg]
      intro hvw
      apply hv
      have hu : ↑h.1.unit⁻¹ * u = 1 := h.1.val_inv_mul
      have hw : w * ↑h.2.unit⁻¹ = 1 := h.2.mul_val_inv
      simp only [Units.val_mul, ← hvw]
      calc v = (↑h.1.unit⁻¹ * u) * v * (w * ↑h.2.unit⁻¹) := by rw [hu, hw, one_mul, mul_one]
        _ = ↑h.1.unit⁻¹ * (u * v * w) * ↑h.2.unit⁻¹ := by ring
        _ = u * v * w * ↑h.1.unit⁻¹ * ↑h.2.unit⁻¹ := by ring
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro v _
    rw [if_neg]
    intro hvw
    apply h
    have ha : IsUnit (u * v * w) := hvw ▸ a.isUnit
    refine ⟨?_, ?_⟩
    · exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left ha)
    · exact isUnit_of_mul_isUnit_right ha

/-- `Kl₃(a)` for a unit `a` as a sum over pairs of units: `Σ_{u,w ∈ (ℤ/D)ˣ} ψ(u + a u⁻¹w⁻¹ + w)`. -/
theorem hyperKloosterman_three_unit (ψ : AddChar (ZMod D) ℂ) (a : (ZMod D)ˣ) :
    hyperKloosterman ψ 3 a = ∑ u : (ZMod D)ˣ, ∑ w : (ZMod D)ˣ, ψ (↑u + ↑(a * u⁻¹ * w⁻¹) + ↑w) := by
  classical
  rw [hyperKloosterman_three]
  simp_rw [inner_sum_unit ψ a]
  let e : (ZMod D)ˣ ↪ ZMod D := ⟨(↑), Units.val_injective⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun u _ hu => ?_),
    Finset.sum_map]
  · apply Finset.sum_congr rfl; intro u _
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun w _ hw => ?_),
      Finset.sum_map]
    · apply Finset.sum_congr rfl; intro w _
      simp only [e, Function.Embedding.coeFn_mk]
      rw [dif_pos ⟨u.isUnit, w.isUnit⟩]
      simp [IsUnit.unit_of_val_units]
    · rw [dif_neg]
      rintro ⟨-, hw'⟩
      exact hw (by simpa [e] using Finset.mem_map_of_mem e (Finset.mem_univ hw'.unit))
  · apply Finset.sum_eq_zero
    intro w _
    rw [dif_neg]
    rintro ⟨hu', -⟩
    exact hu (by simpa [e] using Finset.mem_map_of_mem e (Finset.mem_univ hu'.unit))

omit [NeZero D] in
theorem unit_key (m1 m2 n2 x z : (ZMod D)ˣ) :
    -(m1 * m2 * n2) * (-m1 * x)⁻¹ * (-n2 * z)⁻¹ = -m2 * (x * z)⁻¹ := by
  simp only [neg_mul, inv_neg, mul_inv_rev, neg_neg, mul_neg, neg_mul]
  rw [neg_inj]
  calc m1 * m2 * n2 * (x⁻¹ * m1⁻¹) * (z⁻¹ * n2⁻¹)
      = (m1 * m1⁻¹) * (n2 * n2⁻¹) * (m2 * (z⁻¹ * x⁻¹)) := by ac_rfl
    _ = m2 * (z⁻¹ * x⁻¹) := by simp

/-- **The `w₃` Kloosterman sum at `A = D²` is `D · Kl₃`** (Bump–Friedberg–Goldfeld): for unit weights
`m₁, m₂, n₂`, `S_{w₃}(m, n; D, D²) = D · Kl₃(−m₁m₂n₂; D)`. -/
theorem coxeterKloosterman_eq_hyperKloosterman (ψ : AddChar (ZMod D) ℂ) (m1 m2 n2 : (ZMod D)ˣ) :
    coxeterKloosterman ψ m1 m2 n2 = D • hyperKloosterman ψ 3 ↑(-(m1 * m2 * n2)) := by
  rw [coxeterKloosterman_eq, hyperKloosterman_three_unit]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft (-m1))
  intro x
  apply Fintype.sum_equiv (Equiv.mulLeft (-n2))
  intro z
  simp only [Equiv.coe_mulLeft]
  rw [unit_key]
  congr 1
  simp only [Units.val_mul, Units.val_neg]
  ring

end GaloisForLFunctions.RHTower.GL3
