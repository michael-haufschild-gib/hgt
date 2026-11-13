import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Cyclotomic polynomials are irreducible over a number field away from a fixed modulus

For a number field `L` there is `m₀ ≥ 1` such that `Φ_m` is irreducible over `L` for every
`m ≥ 1` prime to `m₀` (`exists_forall_coprime_irreducible_cyclotomic`).

Let `d(m) = [L(ζ_m) : L]` (`cyclotomicDegree`).
* `d(m)` divides `φ(m)`: the Galois group of `L(ζ_m)/L` embeds into `(ℤ/m)ˣ`
  (`cyclotomicDegree_dvd_totient`);
* `φ(m) ≤ d(m) [L : ℚ]`: the field `ℚ(ζ_m)` of degree `φ(m)` lies in `L(ζ_m)`
  (`totient_le_cyclotomicDegree_mul`);
* `d(m m') ≤ d(m) d(m')` for coprime `m`, `m'`: `L(ζ_{m m'})` is the compositum of `L(ζ_m)`
  and `L(ζ_{m'})` (`cyclotomicDegree_mul_le`).

So the index `e(m) = φ(m)/d(m)` is an integer, at most `[L : ℚ]`, and
`e(m m') ≥ e(m) e(m')` for coprime `m`, `m'`. For `m₀` of maximal index and `m` prime to `m₀`,
`e(m₀) ≥ e(m₀ m) ≥ e(m₀) e(m)` gives `e(m) = 1`: `Φ_m` is the minimal polynomial of `ζ_m`
over `L`.
-/

open Polynomial IntermediateField

noncomputable section

namespace GaloisForLFunctions

/-- Index arithmetic: if `e₀ d₀ = φ₀`, `e d = φ`, `e' d' = φ₀ φ` with `d' ≤ d₀ d` and
`e' ≤ e₀`, then `d = φ`. -/
theorem eq_of_mul_eq_of_le {e₀ e e' d₀ d d' φ₀ φ : ℕ} (h0 : e₀ * d₀ = φ₀) (h1 : e * d = φ)
    (h2 : e' * d' = φ₀ * φ) (h3 : d' ≤ d₀ * d) (h4 : e' ≤ e₀) (hd : 0 < d') (hφ₀ : 0 < φ₀)
    (hφ : 0 < φ) : d = φ := by
  have he₀ : 0 < e₀ := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at h0
    exact hφ₀.ne h0
  have key : e₀ * e * d' ≤ e₀ * 1 * d' :=
    calc e₀ * e * d' ≤ e₀ * e * (d₀ * d) := Nat.mul_le_mul_left _ h3
      _ = e₀ * d₀ * (e * d) := by ring
      _ = e' * d' := by rw [h0, h1, h2]
      _ ≤ e₀ * 1 * d' := by rw [mul_one]; exact Nat.mul_le_mul_right _ h4
  have he : e ≤ 1 := Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_right key hd) he₀
  have he' : e ≠ 0 := fun h => by
    rw [h, zero_mul] at h1
    exact hφ.ne h1
  have he1 : e = 1 := by omega
  rw [← h1, he1, one_mul]

variable (L : Type*) [Field L] [CharZero L]

/-- The degree `[L(ζ_m) : L]` of the `m`-th cyclotomic extension of `L`. -/
def cyclotomicDegree (m : ℕ) : ℕ := Module.finrank L (CyclotomicField m L)

theorem cyclotomicDegree_pos (m : ℕ) [NeZero m] : 0 < cyclotomicDegree L m := by
  haveI := IsCyclotomicExtension.finiteDimensional {m} L (CyclotomicField m L)
  exact Module.finrank_pos

/-- `[L(ζ_m) : L]` divides `φ(m)`: the Galois group embeds into `(ℤ/m)ˣ`. -/
theorem cyclotomicDegree_dvd_totient (m : ℕ) [NeZero m] : cyclotomicDegree L m ∣ m.totient := by
  haveI := IsCyclotomicExtension.finiteDimensional {m} L (CyclotomicField m L)
  haveI := IsCyclotomicExtension.isGalois {m} L (CyclotomicField m L)
  have h := Subgroup.card_dvd_of_injective _
    ((IsCyclotomicExtension.zeta_spec m L (CyclotomicField m L)).autToPow_injective L)
  rwa [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h

/-- `φ(m) ≤ [L(ζ_m) : L] · [L : ℚ]`: the field `ℚ(ζ_m)` has degree `φ(m)` and lies in
`L(ζ_m)`. -/
theorem totient_le_cyclotomicDegree_mul [NumberField L] (m : ℕ) [NeZero m] :
    m.totient ≤ cyclotomicDegree L m * Module.finrank ℚ L := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField m L, IsPrimitiveRoot ζ m :=
    ⟨_, IsCyclotomicExtension.zeta_spec m L (CyclotomicField m L)⟩
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  have h1 : Module.finrank ℚ ℚ⟮ζ⟯ = m.totient := by
    rw [IntermediateField.adjoin.finrank hint, ← cyclotomic_eq_minpoly_rat hζ (NeZero.pos m),
      natDegree_cyclotomic]
  have h2 := LinearMap.finrank_le_finrank_of_injective (f := (ℚ⟮ζ⟯.val).toLinearMap)
    Subtype.val_injective
  rw [h1, ← Module.finrank_mul_finrank ℚ L (CyclotomicField m L)] at h2
  exact h2.trans_eq (mul_comm _ _)

/-- `[L(ζ_{m m'}) : L] ≤ [L(ζ_m) : L] · [L(ζ_{m'}) : L]` for coprime `m`, `m'`. -/
theorem cyclotomicDegree_mul_le {m m' : ℕ} [NeZero m] [NeZero m'] (h : m.Coprime m') :
    cyclotomicDegree L (m * m') ≤ cyclotomicDegree L m * cyclotomicDegree L m' := by
  haveI : NeZero (m * m') := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne m')⟩
  haveI := IsCyclotomicExtension.finiteDimensional {m * m'} L (CyclotomicField (m * m') L)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField (m * m') L, IsPrimitiveRoot ζ (m * m') :=
    ⟨_, IsCyclotomicExtension.zeta_spec (m * m') L (CyclotomicField (m * m') L)⟩
  have hζ₁ : IsPrimitiveRoot (ζ ^ m') m := hζ.pow (NeZero.pos _) (mul_comm m m')
  have hζ₂ : IsPrimitiveRoot (ζ ^ m) m' := hζ.pow (NeZero.pos _) rfl
  haveI := hζ₁.intermediateField_adjoin_isCyclotomicExtension L
  haveI := hζ₂.intermediateField_adjoin_isCyclotomicExtension L
  have e₁ : Module.finrank L L⟮ζ ^ m'⟯ = cyclotomicDegree L m :=
    (IsCyclotomicExtension.algEquiv {m} L L⟮ζ ^ m'⟯
      (CyclotomicField m L)).toLinearEquiv.finrank_eq
  have e₂ : Module.finrank L L⟮ζ ^ m⟯ = cyclotomicDegree L m' :=
    (IsCyclotomicExtension.algEquiv {m'} L L⟮ζ ^ m⟯
      (CyclotomicField m' L)).toLinearEquiv.finrank_eq
  -- `ζ` is a product of powers of `ζ^{m'}` and `ζ^m`
  have hmem : ζ ∈ L⟮ζ ^ m'⟯ ⊔ L⟮ζ ^ m⟯ := by
    have hb := Nat.gcd_eq_gcd_ab m' m
    rw [h.symm.gcd_eq_one, Nat.cast_one] at hb
    have hz : ζ = (ζ ^ m') ^ Nat.gcdA m' m * (ζ ^ m) ^ Nat.gcdB m' m := by
      rw [← zpow_natCast ζ m', ← zpow_natCast ζ m, ← zpow_mul, ← zpow_mul,
        ← zpow_add₀ (hζ.ne_zero (NeZero.ne _)), ← hb, zpow_one]
    have hX : (ζ ^ m') ^ Nat.gcdA m' m * (ζ ^ m) ^ Nat.gcdB m' m ∈ L⟮ζ ^ m'⟯ ⊔ L⟮ζ ^ m⟯ :=
      mul_mem
        (zpow_mem ((le_sup_left : L⟮ζ ^ m'⟯ ≤ L⟮ζ ^ m'⟯ ⊔ L⟮ζ ^ m⟯)
          (mem_adjoin_simple_self L _)) _)
        (zpow_mem ((le_sup_right : L⟮ζ ^ m⟯ ≤ L⟮ζ ^ m'⟯ ⊔ L⟮ζ ^ m⟯)
          (mem_adjoin_simple_self L _)) _)
    rwa [← hz] at hX
  have htop : L⟮ζ ^ m'⟯ ⊔ L⟮ζ ^ m⟯ = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ Algebra.adjoin L {ζ} := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]
      exact Algebra.mem_top
    exact Algebra.adjoin_le (S := (L⟮ζ ^ m'⟯ ⊔ L⟮ζ ^ m⟯).toSubalgebra)
      (Set.singleton_subset_iff.mpr hmem) hx
  calc cyclotomicDegree L (m * m')
      = Module.finrank L ↥(⊤ : IntermediateField L (CyclotomicField (m * m') L)) :=
        IntermediateField.finrank_top'.symm
    _ = Module.finrank L ↥(L⟮ζ ^ m'⟯ ⊔ L⟮ζ ^ m⟯) := by rw [htop]
    _ ≤ Module.finrank L L⟮ζ ^ m'⟯ * Module.finrank L L⟮ζ ^ m⟯ :=
        IntermediateField.finrank_sup_le _ _
    _ = cyclotomicDegree L m * cyclotomicDegree L m' := by rw [e₁, e₂]

/-- If `[L(ζ_m) : L] = φ(m)` then `Φ_m` is irreducible over `L`: it is the minimal polynomial
of `ζ_m`. -/
theorem irreducible_cyclotomic_of_cyclotomicDegree_eq {m : ℕ} [NeZero m]
    (h : cyclotomicDegree L m = m.totient) : Irreducible (cyclotomic m L) := by
  haveI := IsCyclotomicExtension.finiteDimensional {m} L (CyclotomicField m L)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField m L, IsPrimitiveRoot ζ m :=
    ⟨_, IsCyclotomicExtension.zeta_spec m L (CyclotomicField m L)⟩
  have hint : IsIntegral L ζ := Algebra.IsIntegral.isIntegral ζ
  have hdvd : minpoly L ζ ∣ cyclotomic m L := by
    refine minpoly.dvd L ζ ?_
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos m)
  have hdeg : (cyclotomic m L).natDegree ≤ (minpoly L ζ).natDegree := by
    rw [natDegree_cyclotomic, ← h, cyclotomicDegree, (hζ.powerBasis L).finrank,
      IsPrimitiveRoot.powerBasis_dim]
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m L) hdvd hdeg]
  exact minpoly.irreducible hint

/-- **Cyclotomic polynomials are irreducible over a number field away from a fixed modulus.**
There is `m₀ ≥ 1` such that `Φ_m` is irreducible over `L` for every `m ≥ 1` prime to `m₀`. -/
theorem exists_forall_coprime_irreducible_cyclotomic [NumberField L] :
    ∃ m₀ : ℕ, m₀ ≠ 0 ∧ ∀ m : ℕ, m ≠ 0 → m.Coprime m₀ → Irreducible (cyclotomic m L) := by
  have hmul : ∀ m : ℕ, m ≠ 0 →
      m.totient / cyclotomicDegree L m * cyclotomicDegree L m = m.totient := fun m hm => by
    haveI : NeZero m := ⟨hm⟩
    exact Nat.div_mul_cancel (cyclotomicDegree_dvd_totient L m)
  -- the index is at most `[L : ℚ]`
  have hbdd : ∀ m : ℕ, m ≠ 0 → m.totient / cyclotomicDegree L m ≤ Module.finrank ℚ L :=
    fun m hm => by
      haveI : NeZero m := ⟨hm⟩
      refine Nat.le_of_mul_le_mul_right ?_ (cyclotomicDegree_pos L m)
      rw [hmul m hm, mul_comm]
      exact totient_le_cyclotomicDegree_mul L m
  -- a modulus of maximal index
  obtain ⟨m₀, hm₀, hmax⟩ : ∃ m₀ : ℕ, m₀ ≠ 0 ∧ ∀ m : ℕ, m ≠ 0 →
      m.totient / cyclotomicDegree L m ≤ m₀.totient / cyclotomicDegree L m₀ := by
    have hne : {x : ℕ | ∃ m : ℕ, m ≠ 0 ∧ m.totient / cyclotomicDegree L m = x}.Nonempty :=
      ⟨_, 1, one_ne_zero, rfl⟩
    have hbd : BddAbove {x : ℕ | ∃ m : ℕ, m ≠ 0 ∧ m.totient / cyclotomicDegree L m = x} :=
      ⟨Module.finrank ℚ L, by
        rintro _ ⟨m, hm, rfl⟩
        exact hbdd m hm⟩
    obtain ⟨m₀, hm₀, h⟩ := Nat.sSup_mem hne hbd
    exact ⟨m₀, hm₀, fun m hm => h ▸ le_csSup hbd ⟨m, hm, rfl⟩⟩
  refine ⟨m₀, hm₀, fun m hm hcop => ?_⟩
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero m₀ := ⟨hm₀⟩
  have hmm : m₀ * m ≠ 0 := Nat.mul_ne_zero hm₀ hm
  haveI : NeZero (m₀ * m) := ⟨hmm⟩
  have h2 := hmul (m₀ * m) hmm
  have h4 := hmax (m₀ * m) hmm
  rw [Nat.totient_mul hcop.symm] at h2 h4
  exact irreducible_cyclotomic_of_cyclotomicDegree_eq L
    (eq_of_mul_eq_of_le (hmul m₀ hm₀) (hmul m hm) h2 (cyclotomicDegree_mul_le L hcop.symm)
      h4 (cyclotomicDegree_pos L _)
      (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm₀)) (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)))

end GaloisForLFunctions
