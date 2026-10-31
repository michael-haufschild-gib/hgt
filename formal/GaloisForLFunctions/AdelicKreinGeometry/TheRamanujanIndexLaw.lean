import GaloisForLFunctions.AdelicKreinGeometry.TheAdditiveIndexLawOnQModZ

/-!
# The Ramanujan index law

A kernel on `ℤ/N` invariant under the units `(ℤ/N)ˣ` is a combination of Ramanujan sums: its
Fourier coefficients are constant on the conductor classes `{ξ : ord ξ = d}`, `d ∣ N`, which have
`φ(d)` elements.

* **Conductor classes** (`exists_unit_mul_conductorRep`): every `ξ` is a unit multiple of
  `N/ord(ξ)`, so `a_ξ = A_{ord ξ}` with `A_d = a_{N/d}` (`fourierCoeff_eq_conductorRep`).
* **The Ramanujan index law** (`negIndex_zmod_eq_sum_totient`): `κ(k) = Σ_{d ∣ N, A_d < 0} φ(d)`.
* **On `ℚ/ℤ`** (`negIndex_eq_iSup_sum_totient`): a periodic successor invariant under multiplication
  by integers prime to the denominator has `κ(ψ) = sup_N Σ_{d ∣ N, A_d^{(N)} < 0} φ(d)`; every
  negative conductor mode of level `d` costs `φ(d)` squares.

So a conductor-invariant successor of finite index has negative Ramanujan coefficients only at
conductors `d` with `Σ φ(d) ≤ κ`: finitely many conductors, each bounded by `φ(d) ≤ κ`.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

section Level

variable {N : ℕ} [NeZero N]

/-- Invariance under the units of `ℤ/N`. -/
def IsUnitInvariant (k : Multiplicative (ZMod N) → ℂ) : Prop :=
  ∀ (u : (ZMod N)ˣ) (x : ZMod N),
    k (Multiplicative.ofAdd ((u : ZMod N) * x)) = k (Multiplicative.ofAdd x)

/-- The conductor representative `N/d`, of order `d`. -/
def conductorRep (N d : ℕ) : ZMod N := ((N / d : ℕ) : ZMod N)

omit [NeZero N] in
theorem addOrderOf_unit_mul (u : (ZMod N)ˣ) (ξ : ZMod N) :
    addOrderOf ((u : ZMod N) * ξ) = addOrderOf ξ :=
  addOrderOf_injective (AddMonoidHom.mulLeft (u : ZMod N)) (fun x y h => by
    have := congrArg (fun z => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * z) h
    simpa [← mul_assoc] using this) ξ

theorem addOrderOf_divisor {g : ℕ} (hg : g ∣ N) : addOrderOf (g : ZMod N) = N / g := by
  rw [ZMod.addOrderOf_coe g (NeZero.ne N), Nat.gcd_eq_right hg]

/-- **Conductor classes**: `ξ` is a unit multiple of `N/ord(ξ)`. -/
theorem exists_unit_mul_conductorRep (ξ : ZMod N) :
    ∃ u : (ZMod N)ˣ, ξ = (u : ZMod N) * conductorRep N (addOrderOf ξ) := by
  obtain ⟨g, hg, u, hu, rfl⟩ := ZMod.eq_unit_mul_divisor ξ
  refine ⟨hu.unit, ?_⟩
  have hord : addOrderOf (u * (g : ZMod N)) = N / g := by
    rw [← hu.unit_spec, addOrderOf_unit_mul, addOrderOf_divisor hg]
  rw [hord, conductorRep, Nat.div_div_self hg (NeZero.ne N), hu.unit_spec]

theorem fourierCoeff_eq_conductorRep {k : Multiplicative (ZMod N) → ℂ} (hinv : IsUnitInvariant k)
    (ξ : ZMod N) : fourierCoeff k ξ = fourierCoeff k (conductorRep N (addOrderOf ξ)) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_conductorRep ξ
  conv_lhs => rw [hu]
  exact fourierCoeff_unit_mul hinv u _

/-- The Ramanujan coefficient `A_d = a_{N/d}` of conductor `d`. -/
def ramanujanCoeff (k : Multiplicative (ZMod N) → ℂ) (d : ℕ) : ℝ :=
  (fourierCoeff k (conductorRep N d)).re

/-- The conductor class of `d ∣ N` has `φ(d)` elements. -/
theorem card_addOrderOf_eq_totient {d : ℕ} (hd : d ∣ N) :
    (univ.filter fun ξ : ZMod N => addOrderOf ξ = d).card = d.totient := by
  have := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod N) (d := d) (by rw [ZMod.card]; exact hd)
  simpa using this

/-- **The Ramanujan index law**: `κ(k) = Σ_{d ∣ N, A_d < 0} φ(d)`. -/
theorem negIndex_zmod_eq_sum_totient {k : Multiplicative (ZMod N) → ℂ} (hk : IsHermKernel k)
    (hinv : IsUnitInvariant k) :
    negIndex k = ∑ d ∈ N.divisors, if ramanujanCoeff k d < 0 then (d.totient : ℕ∞) else 0 := by
  classical
  rw [negIndex_zmod_eq_card hk]
  have hmaps : ∀ ξ ∈ negCoeffs k, addOrderOf ξ ∈ N.divisors := fun ξ _ =>
    Nat.mem_divisors.mpr ⟨by simpa [ZMod.card] using addOrderOf_dvd_card (x := ξ), NeZero.ne N⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  refine sum_congr rfl fun d hd => ?_
  have hdN := (Nat.mem_divisors.mp hd).1
  by_cases h : ramanujanCoeff k d < 0
  · -- the whole class is negative
    have hfib : (negCoeffs k).filter (fun ξ => addOrderOf ξ = d) =
        univ.filter (fun ξ : ZMod N => addOrderOf ξ = d) := by
      ext ξ
      simp only [negCoeffs, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro hξ
      rw [fourierCoeff_eq_conductorRep hinv, hξ]
      exact h
    rw [hfib, card_addOrderOf_eq_totient hdN, if_pos h]
  · -- no element of the class is negative
    have hfib : (negCoeffs k).filter (fun ξ => addOrderOf ξ = d) = ∅ := by
      ext ξ
      simp only [negCoeffs, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      intro hneg hξ
      rw [fourierCoeff_eq_conductorRep hinv, hξ] at hneg
      exact h hneg
    rw [hfib, if_neg h]
    simp

end Level

/-! ### Conductor-invariant successors on `ℚ/ℤ` -/

/-- Invariance under multiplication by integers prime to the denominator. -/
def IsConductorInvariant (ψ : Multiplicative ℚ → ℂ) : Prop :=
  ∀ (m : ℕ) (b : ℚ), Nat.Coprime m b.den →
    ψ (Multiplicative.ofAdd (m * b)) = ψ (Multiplicative.ofAdd b)

/-- The level kernels of a conductor-invariant periodic successor are unit-invariant. -/
theorem isUnitInvariant_levelKernel {ψ : Multiplicative ℚ → ℂ} (hψ : IsIntPeriodic ψ)
    (hc : IsConductorInvariant ψ) (N : ℕ) [NeZero N] : IsUnitInvariant (levelKernel ψ N) := by
  intro u x
  simp only [levelKernel, toAdd_ofAdd]
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  -- `(ux).val/N = u.val · (x.val/N) − j` for an integer `j`
  set j : ℕ := (u : ZMod N).val * x.val / N
  have hval : (((u : ZMod N) * x).val : ℚ) / N =
      ((u : ZMod N).val : ℚ) * ((x.val : ℚ) / N) + ((-(j : ℤ) : ℤ) : ℚ) := by
    rw [ZMod.val_mul, Int.cast_neg, Int.cast_natCast]
    have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.mod_add_div ((u : ZMod N).val * x.val) N)
    simp only [Nat.cast_add, Nat.cast_mul] at h
    rw [eq_sub_of_add_eq h]
    field_simp
    ring
  rw [hval, hψ.add_int]
  -- `u.val` is prime to `N`, hence to the denominator of `x.val/N`
  have hcop : Nat.Coprime (u : ZMod N).val N := ZMod.val_coe_unit_coprime u
  have hden : ((x.val : ℚ) / N).den ∣ N := by
    have := Rat.den_dvd (x.val : ℤ) (N : ℤ)
    rw [Rat.divInt_eq_div] at this
    push_cast at this
    exact_mod_cast this
  exact hc _ _ (Nat.Coprime.coprime_dvd_right hden hcop)

/-- **The Ramanujan index law on `ℚ/ℤ`.** -/
theorem negIndex_eq_iSup_sum_totient {ψ : Multiplicative ℚ → ℂ} (hk : IsHermKernel ψ)
    (hψ : IsIntPeriodic ψ) (hc : IsConductorInvariant ψ) :
    negIndex ψ = ⨆ N : ℕ, ∑ d ∈ (N + 1).divisors,
      if ramanujanCoeff (levelKernel ψ (N + 1)) d < 0 then (d.totient : ℕ∞) else 0 := by
  rw [negIndex_eq_iSup_card_negCoeffs hk hψ]
  refine iSup_congr fun N => ?_
  rw [← negIndex_zmod_eq_card (isHermKernel_levelKernel hk hψ (N + 1)),
    negIndex_zmod_eq_sum_totient (isHermKernel_levelKernel hk hψ (N + 1))
      (isUnitInvariant_levelKernel hψ hc (N + 1))]

end GaloisForLFunctions.AdelicKreinGeometry
