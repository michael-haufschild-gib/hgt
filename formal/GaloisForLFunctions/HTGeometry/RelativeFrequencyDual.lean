import GaloisForLFunctions.HTGeometry.DivisibleExtension

/-!
# Real coordinates adapted to a subgroup

A family of reals independent over `ℤ` *modulo* a subgroup is independent over `ℚ` modulo the
rational span of that subgroup, because an element of the rational span of a subgroup has an
integral multiple inside the subgroup.  A rationally independent family of a `ℚ`-vector space
extends to real coordinates, so the family admits a `ℚ`-linear functional package that sends it to
the standard basis of `ℝ^r` and kills the subgroup.

This is the algebraic input to the *relative* frequency-rank bound: the parameter subgroup it
produces lies in the kernel of the projection onto the coefficient carrier.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An independent family of a rational vector space extends to real coordinates.** -/
theorem exists_rat_linear_dual_general {V : Type*} [AddCommGroup V] [Module ℚ V] {r : ℕ}
    {lam : Fin r → V} (hind : LinearIndependent ℚ lam) :
    ∃ v : V →ₗ[ℚ] (Fin r → ℝ), ∀ j, v (lam j) = Pi.single j (1 : ℝ) := by
  classical
  set B : Module.Basis (Fin r) ℚ (Submodule.span ℚ (Set.range lam)) := Module.Basis.span hind
    with hB
  set v0 : (Submodule.span ℚ (Set.range lam)) →ₗ[ℚ] (Fin r → ℝ) :=
    B.constr ℚ (fun j => Pi.single j (1 : ℝ)) with hv0
  obtain ⟨v, hv⟩ := v0.exists_extend
  refine ⟨v, fun j => ?_⟩
  have hBj : ((B j : Submodule.span ℚ (Set.range lam)) : V) = lam j := by
    rw [hB, Module.Basis.span_apply hind j]
  have happ : v ((B j : Submodule.span ℚ (Set.range lam)) : V) = v0 (B j) := by
    have := congrArg (fun L : (Submodule.span ℚ (Set.range lam)) →ₗ[ℚ] (Fin r → ℝ) => L (B j)) hv
    simpa using this
  rw [← hBj, happ, hv0]
  simp

/-- **Real coordinates that kill a prescribed rational subspace.** -/
theorem exists_rat_linear_dual_rel {r : ℕ} {lam : Fin r → ℝ} (W : Submodule ℚ ℝ)
    (hind : LinearIndependent ℚ fun j => W.mkQ (lam j)) :
    ∃ v : ℝ →ₗ[ℚ] (Fin r → ℝ), (∀ w ∈ W, v w = 0) ∧
      ∀ j, v (lam j) = Pi.single j (1 : ℝ) := by
  obtain ⟨v', hv'⟩ := exists_rat_linear_dual_general hind
  refine ⟨v'.comp W.mkQ, fun w hw => ?_, fun j => hv' j⟩
  have h0 : W.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hw
  show v' (W.mkQ w) = 0
  rw [h0, map_zero]

/-- **An element of the rational span of a subgroup has an integral multiple in the subgroup.** -/
theorem exists_nsmul_mem_of_mem_span_rat {Γa : AddSubgroup ℝ} {x : ℝ}
    (hx : x ∈ Submodule.span ℚ (Γa : Set ℝ)) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) * x ∈ Γa := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      refine ⟨1, one_pos, ?_⟩
      have : ((1 : ℕ) : ℝ) * y = y := by norm_num
      rw [this]
      exact hy
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      have : ((1 : ℕ) : ℝ) * (0 : ℝ) = 0 := by norm_num
      rw [this]
      exact Γa.zero_mem
  | add y z _ _ hy hz =>
      obtain ⟨n₁, hn₁, hm₁⟩ := hy
      obtain ⟨n₂, hn₂, hm₂⟩ := hz
      refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_⟩
      have hrw : ((n₁ * n₂ : ℕ) : ℝ) * (y + z)
          = n₂ • ((n₁ : ℝ) * y) + n₁ • ((n₂ : ℝ) * z) := by
        push_cast
        simp only [nsmul_eq_mul]
        ring
      rw [hrw]
      exact Γa.add_mem (Γa.nsmul_mem hm₁ n₂) (Γa.nsmul_mem hm₂ n₁)
  | smul q y _ hy =>
      obtain ⟨n, hn, hm⟩ := hy
      refine ⟨n * q.den, Nat.mul_pos hn q.pos, ?_⟩
      have hden : ((q.den : ℝ)) * (q : ℝ) = (q.num : ℝ) := by
        rw [Rat.cast_def]
        field_simp
      have hstep : ((n * q.den : ℕ) : ℝ) * ((q : ℝ) * y)
          = (n : ℝ) * (((q.den : ℝ) * (q : ℝ)) * y) := by
        push_cast
        ring
      have hrw : ((n * q.den : ℕ) : ℝ) * (q • y) = q.num • ((n : ℝ) * y) := by
        rw [Rat.smul_def, hstep, hden]
        simp only [zsmul_eq_mul]
        ring
      rw [hrw]
      exact Γa.zsmul_mem hm q.num

/-- **Integral independence modulo a subgroup is rational independence modulo its span.** -/
theorem linearIndependent_mkQ_of_int {Γa : AddSubgroup ℝ} {r : ℕ} {lam : Fin r → ℝ}
    (hind : ∀ c : Fin r → ℤ, (∑ j, (c j : ℝ) * lam j) ∈ Γa → ∀ j, c j = 0) :
    LinearIndependent ℚ fun j => (Submodule.span ℚ (Γa : Set ℝ)).mkQ (lam j) := by
  classical
  set W : Submodule ℚ ℝ := Submodule.span ℚ (Γa : Set ℝ) with hW
  rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ), Fintype.linearIndependent_iff]
  intro c hc j
  have hsum : W.mkQ (∑ i, (c i : ℝ) * lam i) = 0 := by
    rw [map_sum]
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_zsmul]
    congr 1
    rw [zsmul_eq_mul]
  have hmem : (∑ i, (c i : ℝ) * lam i) ∈ W := by
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hsum
  obtain ⟨n, hn, hnmem⟩ := exists_nsmul_mem_of_mem_span_rat hmem
  have hscaled : (∑ i, (((n : ℤ) * c i : ℤ) : ℝ) * lam i) ∈ Γa := by
    have hrw : (∑ i, (((n : ℤ) * c i : ℤ) : ℝ) * lam i)
        = (n : ℝ) * ∑ i, (c i : ℝ) * lam i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [hrw]
    exact hnmem
  have hzero := hind (fun i => (n : ℤ) * c i) hscaled j
  have hnz : ((n : ℤ)) ≠ 0 := by
    simp only [ne_eq, Int.natCast_eq_zero]
    omega
  exact (mul_eq_zero.mp hzero).resolve_left hnz

end GaloisForLFunctions.HTGeometry
