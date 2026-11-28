import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicPowerClassSeparation

/-! Finite local power classes can be separated in one open quotient of
the compact idele classes. The quotient can refine another open quotient
of the same exponent. -/

noncomputable section

open NumberField IsDedekindDomain Topology GlobalTheory.Kummer

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K : Type} [Field K] [NumberField K]

theorem finite_finiteCompletionPowerClasses {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    (v : HeightOneSpectrum (𝓞 K)) : Finite (PowerClasses (v.adicCompletion K) n) := by
  apply Nat.finite_of_card_ne_zero
  change (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index ≠ 0
  rw [index_power_adicCompletion (n := n) v]
  exact mul_ne_zero (pow_ne_zero _ (NeZero.ne n))
    (pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))

theorem exists_open_power_subgroup_with_local_comap {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    (v : HeightOneSpectrum (𝓞 K))
    (V : Subgroup (CompactIdeleClassQuotient K)) (hV : IsOpen (V : Set (CompactIdeleClassQuotient K)))
    (hVp : compactIdelePowers K n ≤ V) :
    ∃ U : Subgroup (CompactIdeleClassQuotient K), IsOpen (U : Set (CompactIdeleClassQuotient K)) ∧
      compactIdelePowers K n ≤ U ∧ U ≤ V ∧
      U.comap ((toCompactIdeleClassQuotient K).comp (finiteEmbedding v)) =
        (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range := by
  classical
  let F := v.adicCompletion K
  let A := PowerClasses F n
  let A' := {c : A // c ≠ 1}
  let C := CompactIdeleClassQuotient K
  let P := compactIdelePowers K n
  let q := (toCompactIdeleClassQuotient K).comp (finiteEmbedding v)
  letI : Finite A := finite_finiteCompletionPowerClasses (n := n) v
  choose x hx using fun c : A' =>
    QuotientGroup.mk'_surjective (powMonoidHom n : Fˣ →* Fˣ).range c.val
  have hnot (c : A') : x c ∉ (powMonoidHom n : Fˣ →* Fˣ).range := by
    intro h
    exact c.2 ((hx c).symm.trans ((QuotientGroup.eq_one_iff _).mpr h))
  have hcl (c : A') : q (x c) ∉ P.topologicalClosure :=
    (finiteEmbedding_class_mem_closure_powers_iff (n := n) v (x c)).not.mpr (hnot c)
  choose N hN hNp hNx using fun c : A' =>
    exists_open_power_quotient_separating n (q (x c)) (hcl c)
  let U : Subgroup C := V ⊓ ⨅ c : A', N c
  have hu : IsOpen (U : Set C) := by
    change IsOpen ((V : Set C) ∩ ((⨅ c : A', N c : Subgroup C) : Set C))
    rw [Subgroup.coe_iInf]
    exact hV.inter (isOpen_iInter_of_finite hN)
  have hpu : P ≤ U := le_inf hVp (le_iInf hNp)
  refine ⟨U, hu, hpu, inf_le_left, ?_⟩
  apply le_antisymm
  · intro y hy
    apply (QuotientGroup.eq_one_iff y).mp
    by_contra h
    let c : A' := ⟨y, h⟩
    have hc : (x c : A) = (y : A) := hx c
    obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hc
    change z ^ n = (x c)⁻¹ * y at hz
    have he : x c = y / z ^ n := by
      rw [hz, div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, inv_inv]
    have hn : q y ∈ N c := (inf_le_right.trans (iInf_le N c)) (show q y ∈ U from hy)
    have hpz : q z ^ n ∈ N c := hNp c ⟨q z, rfl⟩
    apply hNx c
    rw [he, map_div, map_pow]
    exact (N c).div_mem hn hpz
  · rintro _ ⟨z, rfl⟩
    change q (z ^ n) ∈ U
    rw [map_pow]
    exact hpu ⟨q z, rfl⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_open_power_subgroup_with_local_comap
