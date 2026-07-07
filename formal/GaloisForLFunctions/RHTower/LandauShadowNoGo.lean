/-
Landau positivity's mod-`2^k` shadow is blind to every nontrivial zero.

The Euler / von Mangoldt positivity `Λ(n) ≥ 0` is a **real-coefficient** structure: `log ζ`
has real Dirichlet coefficients, so `log ζ(s̄) = conj(log ζ(s))` and the whole object is
symmetric under complex conjugation `s ↦ s̄`. Its natural discrete invariant is therefore the
mod-`2` count of the zero divisor read across the **real axis** — the fixed set of conjugation.

This module proves that invariant is vacuous. For a conjugation-symmetric zero configuration,
the mod-`2` total multiplicity equals the multiplicity **on the real axis** (`conj_equivariant_parity`);
and a configuration all of whose points lie off the real axis has **even** total multiplicity —
its mod-`2` shadow is trivially `1` (`conj_shadow_trivial_of_offaxis`). Every nontrivial zero of
ξ has nonzero imaginary part, so the conjugation shadow detects none of them.

The contrast with the functional equation is exact. The **same** configuration, read across the
**critical line** `Re s = 1/2` (the fixed set of `s ↦ 1 − s̄`, the FE's axis), has mod-`2` shadow
equal to its on-critical-line count — the nonvacuous invariant Hardy's method uses. Landau
positivity lives on the wrong axis: its symmetry is the real axis, orthogonal to the critical
line where the zeros sit. The FE supplies the useful axis, but that shadow is a line phenomenon
and goes silent off the line.

`landau_conj_shadow_vs_fe_line_shadow` states both readings of one configuration side by side:
conjugation → trivial, line-reflection → the on-line count. So Landau positivity **alone**
produces no mod-`2^k` detector for nontrivial zeros; the two constraints are separately blind,
and neither's shadow crosses into the strip without an added flow (Bohr lift or analytic
continuation across the wall `Re s = 1`) that a constraint-only reading refuses.
-/
import GaloisForLFunctions.RHTower.MirrorTransport

noncomputable section

namespace RHTower

open Complex Finset

/-! ### §1 The conjugation-axis equivariant parity -/

/-- **Conjugation equivariant parity.**  For a zero configuration symmetric under complex
conjugation (`ρc (σf i) = conj (ρc i)`, matched multiplicities, `σf` an involution), the mod-`2`
total multiplicity equals the multiplicity **on the real axis** `{im = 0}` — the fixed set of
conjugation.  Off-axis points pair `ρ ↔ ρ̄` and cancel mod `2`. -/
theorem conj_equivariant_parity {ι : Type*}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σf : ι → ι)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσρ : ∀ i ∈ s, ρc (σf i) = (starRingEnd ℂ) (ρc i))
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i) :
    ((-1 : ℂ)) ^ (∑ i ∈ s, m i)
      = (-1) ^ (∑ i ∈ s.filter (fun i => (ρc i).im = 0), m i) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => (ρc i).im = 0) m]
  have heven : Even (∑ i ∈ s.filter (fun i => ¬(ρc i).im = 0), m i) := by
    rw [even_iff_two_dvd,
      ← ZMod.natCast_eq_zero_iff (∑ i ∈ s.filter (fun i => ¬(ρc i).im = 0), m i) 2]
    push_cast
    refine Finset.sum_involution (fun i _ => σf i) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨his, -⟩ := Finset.mem_filter.mp hi
      show (m i : ZMod 2) + (m (σf i) : ZMod 2) = 0
      rw [hσm i his]
      exact CharTwo.add_self_eq_zero _
    · intro i hi _
      obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
      intro heq
      have heq' : σf i = i := heq
      apply hnot
      have hρeq : ρc i = (starRingEnd ℂ) (ρc i) := by
        rw [← hσρ i his, heq']
      have him := congrArg Complex.im hρeq
      rw [Complex.conj_im] at him
      linarith
    · intro i hi
      obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
      show σf i ∈ s.filter (fun i => ¬(ρc i).im = 0)
      rw [Finset.mem_filter]
      refine ⟨hσmem i his, ?_⟩
      rw [hσρ i his, Complex.conj_im]
      intro heq
      apply hnot
      linarith
    · intro i hi
      show σf (σf i) = i
      exact hσinv i (Finset.mem_filter.mp hi).1
  rw [pow_add, heven.neg_one_pow, mul_one]

/-! ### §2 The blindness: an off-real-axis configuration has trivial conjugation shadow -/

/-- **The Landau shadow is trivial on off-axis configurations.**  A conjugation-symmetric
configuration whose points all lie off the real axis (every `(ρc i).im ≠ 0`) has **even** total
multiplicity, so its mod-`2` conjugation shadow is `1`.  Nontrivial zeros all have `im ≠ 0`, so
the conjugation shadow — the natural mod-`2` invariant of the real-coefficient Euler positivity —
detects none of them. -/
theorem conj_shadow_trivial_of_offaxis {ι : Type*}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σf : ι → ι)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσρ : ∀ i ∈ s, ρc (σf i) = (starRingEnd ℂ) (ρc i))
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i)
    (hoff : ∀ i ∈ s, (ρc i).im ≠ 0) :
    ((-1 : ℂ)) ^ (∑ i ∈ s, m i) = 1 := by
  rw [conj_equivariant_parity s ρc m σf hσmem hσρ hσm hσinv]
  have hempty : s.filter (fun i => (ρc i).im = 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact fun i hi => hoff i hi
  rw [hempty, Finset.sum_empty, pow_zero]

/-! ### §3 The contrast: Landau's axis is blind where the FE's axis sees -/

/-- **The two shadows of one configuration.**  Take a zero configuration off the real axis that
is symmetric under **both** conjugation `σc` (axis = real axis) and the critical-line reflection
`σℓ` (axis `Re = 1/2`, the FE's involution `s ↦ 1 − s̄`).  Then:

* its **conjugation** shadow — the natural mod-`2` invariant of the real-coefficient Landau
  positivity — is trivially `1` (blind to every point);
* its **critical-line** shadow equals the on-critical-line count `(-1)^{Σ_{Re = 1/2} m}` — the
  nonvacuous invariant.

Landau positivity is symmetric about the real axis, orthogonal to the critical line where the
zeros live: its shadow cannot see them.  The functional equation supplies the axis that can, but
that is a line reading, not something Landau positivity provides. -/
theorem landau_conj_shadow_vs_fe_line_shadow {ι : Type*}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σc σℓ : ι → ι)
    (hσcmem : ∀ i ∈ s, σc i ∈ s) (hσcρ : ∀ i ∈ s, ρc (σc i) = (starRingEnd ℂ) (ρc i))
    (hσcm : ∀ i ∈ s, m (σc i) = m i) (hσcinv : ∀ i ∈ s, σc (σc i) = i)
    (hσℓmem : ∀ i ∈ s, σℓ i ∈ s) (hσℓρ : ∀ i ∈ s, ρc (σℓ i) = lineReflection (1 / 2) (ρc i))
    (hσℓm : ∀ i ∈ s, m (σℓ i) = m i) (hσℓinv : ∀ i ∈ s, σℓ (σℓ i) = i)
    (hoff : ∀ i ∈ s, (ρc i).im ≠ 0) :
    (((-1 : ℂ)) ^ (∑ i ∈ s, m i) = 1) ∧
      (((-1 : ℂ)) ^ (∑ i ∈ s, m i)
        = (-1) ^ (∑ i ∈ s.filter (fun i => (ρc i).re = 1 / 2), m i)) :=
  ⟨conj_shadow_trivial_of_offaxis s ρc m σc hσcmem hσcρ hσcm hσcinv hoff,
    neg_one_pow_sum_reflection_equivariant s ρc m σℓ hσℓmem hσℓρ hσℓm hσℓinv⟩

/-- **Consequence — the two axes force the on-line count to be even.**  Combining the two
readings of §3: for a configuration off the real axis, symmetric under both involutions, the
on-critical-line count is itself even.  The two shadows together say nothing about the off-line
multiplicities — the whole parity content collapses onto the (real-axis-empty, hence even)
conjugation reading.  This is the precise sense in which Landau positivity's mod-`2` shadow is
vacuous for the off-line question. -/
theorem fe_line_count_even_of_offaxis_conj_symmetric {ι : Type*}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σc σℓ : ι → ι)
    (hσcmem : ∀ i ∈ s, σc i ∈ s) (hσcρ : ∀ i ∈ s, ρc (σc i) = (starRingEnd ℂ) (ρc i))
    (hσcm : ∀ i ∈ s, m (σc i) = m i) (hσcinv : ∀ i ∈ s, σc (σc i) = i)
    (hσℓmem : ∀ i ∈ s, σℓ i ∈ s) (hσℓρ : ∀ i ∈ s, ρc (σℓ i) = lineReflection (1 / 2) (ρc i))
    (hσℓm : ∀ i ∈ s, m (σℓ i) = m i) (hσℓinv : ∀ i ∈ s, σℓ (σℓ i) = i)
    (hoff : ∀ i ∈ s, (ρc i).im ≠ 0) :
    ((-1 : ℂ)) ^ (∑ i ∈ s.filter (fun i => (ρc i).re = 1 / 2), m i) = 1 := by
  obtain ⟨htrivial, hline⟩ :=
    landau_conj_shadow_vs_fe_line_shadow s ρc m σc σℓ
      hσcmem hσcρ hσcm hσcinv hσℓmem hσℓρ hσℓm hσℓinv hoff
  rw [← hline, htrivial]

/-! ### §4 The kill on the actual ξ divisor -/

/-- **Landau's conjugation shadow is blind to ξ's nontrivial zeros.**  For any finite,
conjugation-closed set of off-real-axis points, the mod-`2` total vanishing order of ξ is even.
The reality pairing `xi_orderAt_conj` supplies the matched multiplicities; conjugation is the
symmetry of the real-coefficient Euler positivity; every point is off the real axis (as every
nontrivial zero is).  So the conjugation shadow — Landau positivity's natural mod-`2` invariant —
carries no information about the off-line (indeed any nontrivial) zeros of ξ. -/
theorem xi_conj_shadow_blind (s : Finset ℂ)
    (hclosed : ∀ ρ ∈ s, (starRingEnd ℂ) ρ ∈ s)
    (hoff : ∀ ρ ∈ s, ρ.im ≠ 0) :
    ((-1 : ℂ)) ^ (∑ ρ ∈ s, (analyticOrderAt xi ρ).toNat) = 1 :=
  conj_shadow_trivial_of_offaxis s id (fun ρ => (analyticOrderAt xi ρ).toNat)
    (starRingEnd ℂ) hclosed (fun _ _ => rfl)
    (fun ρ _ => congrArg ENat.toNat (xi_orderAt_conj ρ))
    (fun ρ _ => Complex.conj_conj ρ) hoff

/-- **The aggregate total order of any off-axis conjugation-closed ξ configuration is even.**
The mod-`2` form of `xi_conj_shadow_blind`: pairing `ρ ↔ ρ̄` forces `2 ∣ Σ ord`.  This is
aggregate, never per-zero: the same pairing makes the mod-`2^k` conjugation count `2·(Σ over
pair representatives)`, an even multiple carrying only the aggregate — so no conjugation-derived
invariant reaches the per-zero divisibility `2^k ∣ ord_ρ` that `RHLadder k` needs. -/
theorem xi_conj_order_sum_even (s : Finset ℂ)
    (hclosed : ∀ ρ ∈ s, (starRingEnd ℂ) ρ ∈ s)
    (hoff : ∀ ρ ∈ s, ρ.im ≠ 0) :
    Even (∑ ρ ∈ s, (analyticOrderAt xi ρ).toNat) :=
  (neg_one_pow_eq_one_iff_even (R := ℂ) (by norm_num)).mp (xi_conj_shadow_blind s hclosed hoff)

end RHTower
