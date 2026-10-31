import GaloisForLFunctions.AdelicKreinGeometry.TheArchimedeanGluingFormula
import GaloisForLFunctions.HTGeometry.RationalTameData

/-!
# Prime towers glue at full index

The boost hyperplane `ℓ = 0` costs nothing for dilation data that do not see some direction in which
the boost moves.

* **Periodic data** (`boostPolarIndex_eq_negIndex_of_periodic`): if `K(v₀u) = K(u)` for one slope
  `v₀ ≠ 1`, a negative family `F` and its dilate `v₀F`, weighted `c` and `−v₀^{1/2}c`, carry the form
  `(1 − v₀^{1/2})² Q_F(c)` on `ℓ = 0`; so `κ^{(½)}(K) = κ(K)` and the archimedean gluing costs exactly
  one square (`negIndex_archGlue_eq_of_periodic`).
* **A prime tower** (`negIndex_archGlue_tower`): a kernel `k` on the `p`-tower `ℤ`, read through the
  valuation `v_p`, glued to `−c|b|` has index `κ(k) + 1`. A prime `q ≠ p` moves the boost and is
  invisible to the tower.

So every finite set of local towers, matched or not, is glued by the archimedean place with exactly
one extra square: the local–global formula `κ(global) = κ(towers) + 1` holds whenever the towers miss a
prime. Weil's kernel sees every prime; for it the hyperplane is free for a different reason, the
sub-boost growth of its zero side.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- **Dilation-periodic data are glued at full index.** -/
theorem boostPolarIndex_eq_negIndex_of_periodic {K : posUnits → ℂ} {v₀ : posUnits} (hv₀ : v₀ ≠ 1)
    (hper : ∀ u, K (v₀ * u) = K u) : boostPolarIndex K = negIndex K := by
  classical
  refine le_antisymm (boostPolarIndex_le_negIndex K) (negIndex_le_iff.mpr fun n F => ?_)
  have hper' : ∀ u, K (v₀⁻¹ * u) = K u := fun u => by
    rw [← hper (v₀⁻¹ * u), mul_inv_cancel_left]
  set t : ℝ := ((((v₀ : posUnits) : ℚˣ) : ℚ) : ℝ)
  have ht : 0 < t := posUnits_val_pos v₀
  set β : ℝ := t ^ (1 / 2 : ℝ)
  have hβ1 : β ≠ 1 := fun h => by
    apply hv₀
    have h2 : t = 1 := by
      have := congrArg (fun x : ℝ => x ^ (2 : ℝ)) h
      simp only [β, ← Real.rpow_mul ht.le, Real.one_rpow] at this
      norm_num at this
      exact this
    have h3 : ((((v₀ : posUnits) : ℚˣ) : ℚ) : ℝ) = 1 := h2
    apply Subtype.ext; apply Units.ext
    simp only [OneMemClass.coe_one, Units.val_one]
    exact_mod_cast h3
  -- the doubled family `F ⊔ v₀F`
  set G : Fin (n + n) → posUnits := Fin.append F fun i => v₀ * F i
  set L : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + n) → ℂ) :=
    { toFun := fun c => Fin.append c fun i => -(β : ℂ) * c i
      map_add' := fun c d => by
        ext a
        induction a using Fin.addCases with
        | left i => simp only [Fin.append_left, Pi.add_apply]
        | right i => simp only [Fin.append_right, Pi.add_apply]; ring
      map_smul' := fun z c => by
        ext a
        induction a using Fin.addCases with
        | left i => simp only [Fin.append_left, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        | right i =>
          simp only [Fin.append_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hG1 : ∀ i j, gram K G (Fin.castAdd n i) (Fin.castAdd n j) = gram K F i j := fun i j => by
    simp only [gram, G, Fin.append_left]
  have hG2 : ∀ i j, gram K G (Fin.castAdd n i) (Fin.natAdd n j) = gram K F i j := fun i j => by
    simp only [gram, G, Fin.append_left, Fin.append_right]
    rw [mul_left_comm, hper]
  have hG3 : ∀ i j, gram K G (Fin.natAdd n i) (Fin.castAdd n j) = gram K F i j := fun i j => by
    simp only [gram, G, Fin.append_left, Fin.append_right]
    rw [mul_inv_rev, mul_comm (F i)⁻¹ v₀⁻¹, mul_assoc, hper']
  have hG4 : ∀ i j, gram K G (Fin.natAdd n i) (Fin.natAdd n j) = gram K F i j := fun i j => by
    simp only [gram, G, Fin.append_right]
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  -- the form of the doubled vector
  have hform : ∀ c, hermQuad (gram K G) (L c) = (1 - β) ^ 2 * hermQuad (gram K F) c := by
    intro c
    rw [hermQuad_gram, hermQuad_gram, ← Complex.re_ofReal_mul]
    congr 1
    have hgram : ∀ a b, gram K G a b = K ((G a)⁻¹ * G b) := fun a b => rfl
    simp only [← hgram, Fin.sum_univ_add, L, LinearMap.coe_mk, AddHom.coe_mk, Fin.append_left,
      Fin.append_right, hG1, hG2, hG3, hG4, map_mul, map_neg, Complex.conj_ofReal, mul_sum,
      ← sum_add_distrib]
    simp only [gram]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    push_cast; ring
  -- the doubled vectors lie on `ℓ = 0`
  have hroot : ∀ i, (((((v₀ * F i : posUnits) : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) =
      t ^ (-(1 / 2 : ℝ)) * ((((F i : ℚˣ) : ℚ) : ℝ)) ^ (-(1 / 2 : ℝ)) := fun i => by
    simp only [Subgroup.coe_mul, Units.val_mul, Rat.cast_mul, t]
    exact Real.mul_rpow (posUnits_val_pos _).le (posUnits_val_pos _).le
  have hβt : β * t ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.rpow_neg ht.le, mul_inv_cancel₀ (by positivity)]
  have hker : ∀ c, L c ∈ LinearMap.ker (boostMassU G) := fun c => by
    rw [LinearMap.mem_ker]
    simp only [boostMassU, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_add, L, G,
      Fin.append_left, Fin.append_right, hroot, ← sum_add_distrib]
    refine sum_eq_zero fun i _ => ?_
    have : ((β * t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by rw [hβt]; simp
    push_cast at this ⊢
    linear_combination (-(c i * (((((F i : ℚˣ) : ℚ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) * this
  -- transport a negative subspace
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-gram K F)
  set bW := Module.finBasis ℂ W
  set L' : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (Fin (n + n) → ℂ) :=
    L ∘ₗ W.subtype ∘ₗ bW.equivFun.symm.toLinearMap
  have hneg : ∀ a, a ≠ 0 → hermQuad (gram K G) (L' a) < 0 := fun a ha => by
    have hw0 : (bW.equivFun.symm a : Fin n → ℂ) ≠ 0 := fun h =>
      ha (bW.equivFun.symm.injective (Subtype.ext (by rw [h, map_zero]; rfl)))
    have hpos := hW _ (bW.equivFun.symm a).2 hw0
    rw [hermQuad_neg] at hpos
    have h1 : 0 < (1 - β) ^ 2 := by
      have : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ1)
      positivity
    simp only [L', LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe]
    rw [hform]
    exact mul_neg_of_pos_of_neg h1 (by linarith)
  have h := card_le_negIndexOn_of_forall_neg (gram K G) _ L' (fun a => hker _) hneg
  rw [Fintype.card_fin] at h
  have h2 : hermNegIndex (gram K F) = Module.finrank ℂ W := hrank.symm
  calc (hermNegIndex (gram K F) : ℕ∞)
      ≤ (negIndexOn (gram K G) (LinearMap.ker (boostMassU G)) : ℕ∞) := Nat.cast_le.mpr (h2 ▸ h)
    _ ≤ boostPolarIndex K := negIndexOn_le_boostPolarIndex K G

/-- Periodic data cost exactly one square more: `κ(K(|a|) − c|a|^{−1/2}|b|) = κ(K) + 1`. -/
theorem negIndex_archGlue_eq_of_periodic {K : posUnits → ℂ} (hK : IsHermKernel K) {v₀ : posUnits}
    (hv₀ : v₀ ≠ 1) (hper : ∀ u, K (v₀ * u) = K u) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue K c) = negIndex K + 1 := by
  rw [negIndex_archGlue_eq hK hc, boostPolarIndex_eq_negIndex_of_periodic hv₀ hper]

/-! ### A prime tower -/

section Tower

variable (p : ℕ) [Fact p.Prime]

/-- The valuation `v_p` on the positive slopes. -/
def towerVal : posUnits →* Multiplicative ℤ := (ratPadicValHom p).comp posUnits.subtype

/-- The positive slope `q` for a prime `q`. -/
def primePos (q : ℕ) [Fact q.Prime] : posUnits :=
  ⟨Units.mk0 (q : ℚ) (by exact_mod_cast (Fact.out : q.Prime).ne_zero), by
    show (0 : ℚ) < q; exact_mod_cast (Fact.out : q.Prime).pos⟩

theorem towerVal_primePos_self : towerVal p (primePos p) = Multiplicative.ofAdd 1 := by
  simp [towerVal, primePos, ratPadicValHom, padicValRat.self (Fact.out : p.Prime).one_lt]

theorem towerVal_primePos_ne {q : ℕ} [Fact q.Prime] (hpq : p ≠ q) :
    towerVal p (primePos q) = 1 := by
  simp only [towerVal, primePos, ratPadicValHom, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, padicValRat.of_nat]
  rw [padicValNat_primes hpq]
  rfl

theorem towerVal_surjective : Function.Surjective (towerVal p) := fun m => by
  refine ⟨primePos p ^ (Multiplicative.toAdd m), ?_⟩
  rw [map_zpow, towerVal_primePos_self, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]

/-- **A prime tower glued at the archimedean place**: a Hermitian kernel `k` on the `p`-tower, read
through `v_p` and glued to `−c|b|`, has exactly `κ(k) + 1` negative squares. -/
theorem negIndex_archGlue_tower {k : Multiplicative ℤ → ℂ} (hk : IsHermKernel k) {c : ℝ}
    (hc : 0 < c) : negIndex (archGlue (k ∘ towerVal p) c) = negIndex k + 1 := by
  -- a second prime moves the boost and is invisible to the tower
  obtain ⟨q, hq, hpq⟩ : ∃ q : ℕ, q.Prime ∧ p ≠ q := by
    by_cases h2 : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, h2⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hv₀ : primePos q ≠ 1 := fun h => by
    have := congrArg (fun u : posUnits => ((u : ℚˣ) : ℚ)) h
    simp only [primePos, Units.val_mk0, OneMemClass.coe_one, Units.val_one] at this
    have : (q : ℚ) = 1 := this
    exact hq.one_lt.ne' (by exact_mod_cast this)
  have hper : ∀ u, (k ∘ towerVal p) (primePos q * u) = (k ∘ towerVal p) u := fun u => by
    simp only [Function.comp_apply, map_mul, towerVal_primePos_ne p hpq, one_mul]
  rw [negIndex_archGlue_eq_of_periodic (hk.comp _) hv₀ hper hc,
    negIndex_comp_of_surjective _ _ (towerVal_surjective p)]

end Tower

end GaloisForLFunctions.AdelicKreinGeometry
