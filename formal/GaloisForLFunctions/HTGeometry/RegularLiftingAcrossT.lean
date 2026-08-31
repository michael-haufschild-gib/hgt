import GaloisForLFunctions.HTGeometry.CohenMacaulayDepth

/-!
# Lifting regularity across a nonzerodivisor

A nonzerodivisor on the quotient by `t` is a nonzerodivisor upstairs, provided `t` itself is a
nonzerodivisor and nothing is infinitely divisible by `t`:

```text
isSMulRegular_of_isSMulRegular_quotient
    ** t regular, M t-separated, x regular on M ⧸ tM ⟹ x regular on M **
isSMulRegular_quotient_of_isSMulRegular_quotient
    ** t regular on M and x regular on M ⧸ tM ⟹ t regular on M ⧸ xM **
```

The first is a descent: anything killed by `x` is divisible by `t`, and dividing preserves being
killed by `x`, so it is divisible by every power of `t` and therefore zero.  The second is what
allows the first to be applied again after passing to `M ⧸ xM`.

Separatedness, however, is *not* inherited by `M ⧸ xM`, and the failure is not subtle: over
`M = K[t]` with `x = 1 - t`, the module `M` is `t`-separated and `x` is regular on `M ⧸ tM = K`, yet
`M ⧸ xM ≅ K` has `t` acting as the identity, so every power of `t` is surjective on it.  Iterating
the lift along a sequence therefore needs a separatedness input at each stage — for instance a
grading in which `t` has negative degree, where the components of a nonzero element are supported in
degrees bounded above.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

theorem exists_smul_of_mem_smul_top {t : R} {z : M} (hz : z ∈ t • (⊤ : Submodule R M)) :
    ∃ z₁ : M, z = t • z₁ := by
  rw [Submodule.mem_smul_pointwise_iff_exists] at hz
  obtain ⟨z₁, _, hz₁⟩ := hz
  exact ⟨z₁, hz₁.symm⟩

theorem smul_mem_pow_succ_smul_top {t : R} {n : ℕ} {z : M}
    (hz : z ∈ (t ^ n) • (⊤ : Submodule R M)) :
    t • z ∈ (t ^ (n + 1)) • (⊤ : Submodule R M) := by
  rw [Submodule.mem_smul_pointwise_iff_exists] at hz ⊢
  obtain ⟨z₁, -, hz₁⟩ := hz
  refine ⟨z₁, Submodule.mem_top, ?_⟩
  rw [← hz₁, pow_succ, mul_smul]
  exact (smul_comm t (t ^ n) z₁).symm

/-- **Regularity lifts across a nonzerodivisor.**  If `t` is a nonzerodivisor on `M`, `M` is
`t`-adically separated, and `x` is a nonzerodivisor on `M ⧸ tM`, then `x` is a nonzerodivisor on
`M`.  Descending along `t` shows that anything killed by `x` is infinitely divisible by `t`. -/
theorem isSMulRegular_of_isSMulRegular_quotient {t x : R}
    (ht : IsSMulRegular M t)
    (hsep : ∀ u : M, (∀ n : ℕ, u ∈ (t ^ n) • (⊤ : Submodule R M)) → u = 0)
    (hx : IsSMulRegular (M ⧸ (t • (⊤ : Submodule R M))) x) :
    IsSMulRegular M x := by
  have key : ∀ n : ℕ, ∀ z : M, x • z = 0 → z ∈ (t ^ n) • (⊤ : Submodule R M) := by
    intro n
    induction n with
    | zero => intro z _; simp
    | succ n ih =>
      intro z hz
      have hquot : x • (Submodule.Quotient.mk z : M ⧸ (t • (⊤ : Submodule R M)))
          = x • (0 : M ⧸ (t • (⊤ : Submodule R M))) := by
        rw [smul_zero, ← Submodule.Quotient.mk_smul, hz]
        rfl
      have hz0 : (Submodule.Quotient.mk z : M ⧸ (t • (⊤ : Submodule R M))) = 0 := hx hquot
      rw [Submodule.Quotient.mk_eq_zero] at hz0
      obtain ⟨z₁, rfl⟩ := exists_smul_of_mem_smul_top hz0
      have hx1 : x • z₁ = 0 := by
        refine ht ?_
        show t • (x • z₁) = t • (0 : M)
        rw [smul_zero, smul_comm]
        exact hz
      exact smul_mem_pow_succ_smul_top (ih z₁ hx1)
  intro u v huv
  have hz : x • (u - v) = 0 := by
    rw [smul_sub]
    have : x • u = x • v := huv
    rw [this, sub_self]
  have := hsep (u - v) (fun n => key n (u - v) hz)
  exact sub_eq_zero.mp this

/-- **The nonzerodivisor survives the quotient.**  If `t` is a nonzerodivisor on `M` and `x` is one
on `M ⧸ tM`, then `t` is a nonzerodivisor on `M ⧸ xM`.  This is the step that lets the lifting be
iterated along a sequence. -/
theorem isSMulRegular_quotient_of_isSMulRegular_quotient {t x : R}
    (ht : IsSMulRegular M t)
    (hx : IsSMulRegular (M ⧸ (t • (⊤ : Submodule R M))) x) :
    IsSMulRegular (M ⧸ (x • (⊤ : Submodule R M))) t := by
  have key : ∀ z : M, t • (Submodule.Quotient.mk z : M ⧸ (x • (⊤ : Submodule R M))) = 0 →
      (Submodule.Quotient.mk z : M ⧸ (x • (⊤ : Submodule R M))) = 0 := by
    intro z hz
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨v, hv⟩ := exists_smul_of_mem_smul_top hz
    have hmemt : x • v ∈ t • (⊤ : Submodule R M) := by
      rw [← hv]
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨z, Submodule.mem_top, rfl⟩
    have hquot : x • (Submodule.Quotient.mk v : M ⧸ (t • (⊤ : Submodule R M)))
        = x • (0 : M ⧸ (t • (⊤ : Submodule R M))) := by
      rw [smul_zero, ← Submodule.Quotient.mk_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hmemt
    have hv0 : (Submodule.Quotient.mk v : M ⧸ (t • (⊤ : Submodule R M))) = 0 := hx hquot
    rw [Submodule.Quotient.mk_eq_zero] at hv0
    obtain ⟨v₁, rfl⟩ := exists_smul_of_mem_smul_top hv0
    have hzx : z = x • v₁ := by
      refine ht ?_
      show t • z = t • (x • v₁)
      rw [hv, smul_comm]
    rw [hzx, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨v₁, Submodule.mem_top, rfl⟩
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | H u =>
    induction b using Submodule.Quotient.induction_on with
    | H v =>
      have hsub : t • (Submodule.Quotient.mk (u - v) :
          M ⧸ (x • (⊤ : Submodule R M))) = 0 := by
        rw [Submodule.Quotient.mk_sub, smul_sub]
        have h1 : t • (Submodule.Quotient.mk u : M ⧸ (x • (⊤ : Submodule R M)))
            = t • (Submodule.Quotient.mk v : M ⧸ (x • (⊤ : Submodule R M))) := hab
        rw [h1, sub_self]
      have := key (u - v) hsub
      rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
      exact this

end GaloisForLFunctions.HTGeometry
