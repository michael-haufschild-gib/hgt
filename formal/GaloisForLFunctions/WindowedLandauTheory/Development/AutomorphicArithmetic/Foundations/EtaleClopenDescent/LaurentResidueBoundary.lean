import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveResidueAtOrigin

/-! Projective Laurent residues annihilate regular top forms on each proper
intersection of the standard cover. -/

noncomputable section

namespace GlobalTheory.PD

variable {F : Type} [Field F] {d : ℕ}

private theorem prod_zpow_add (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j, x j ^ (m j + n j) = (∏ j, x j ^ m j) * ∏ j, x j ^ n j := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (hx j) _ _

private def chartMonomials (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (I : Finset (Fin (d + 1))) : Submonoid F where
  carrier := {f | ∃ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 ∧ (∀ j ∉ I, 0 ≤ m j) ∧ f = ∏ j, x j ^ m j}
  one_mem' := ⟨0, by simp, fun _ _ => le_rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm, hm', rfl⟩ ⟨n, hn, hn', rfl⟩
    refine ⟨m + n, ?_, fun j hj => add_nonneg (hm' j hj) (hn' j hj), ?_⟩
    · simp [Finset.sum_add_distrib, hm, hn]
    · simp only [Pi.add_apply]; exact (prod_zpow_add x hx m n).symm

private theorem prod_single_sub (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i j : Fin (d + 1)) :
    ∏ l, x l ^ ((Pi.single j 1 : Fin (d + 1) → ℤ) l - (Pi.single i 1 : Fin (d + 1) → ℤ) l) = x j / x i := by
  simp_rw [zpow_sub₀ (hx _)]
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [Fintype.prod_eq_single j (fun l hl => by simp [Pi.single_apply, hl])]; simp
  · rw [Fintype.prod_eq_single i (fun l hl => by simp [Pi.single_apply, hl])]; simp

private theorem prod_exp (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i₀ : Fin (d + 1)) :
    (∏ j, x j ^ ((1 : ℤ) - if j = i₀ then ((d : ℤ) + 1) else 0)) * ∏ j, x i₀ / x j = 1 := by
  simp_rw [zpow_sub₀ (hx _), zpow_one]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  have hq : ∏ j, x j ^ (if j = i₀ then ((d : ℤ) + 1) else 0) = x i₀ ^ (d + 1) := by
    rw [Fintype.prod_eq_single i₀ (fun l hl => by simp [hl])]
    rw [if_pos rfl, show ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hq]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : ∏ j, x j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hx j
  have h1 := hx i₀
  field_simp

/-- The residue vanishes on a chart intersection missing a coordinate
whenever multiplication by the chart volume denominator gives a regular function. -/
theorem residue_eq_zero_of_missing_chart {k : Type} [Field k] [Algebra k F]
    {x : Fin (d + 1) → F} (hx : IsPd k x) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    {i i₀ : Fin (d + 1)} {I : Finset (Fin (d + 1))} (hi : i ∉ I) (hi₀ : i₀ ∈ I)
    (y : F) (h₁ : (∏ j, x i₀ / x j) * y ∈ rA k x I) : ρ y = 0 := by
  have hne := hx.ne
  have hii₀ : i ≠ i₀ := fun h => hi (h.symm ▸ hi₀)
  have hz : (∏ j, x i₀ / x j) * y ∈ Submodule.span k (chartMonomials x hne I : Set F) := by
    rw [rA, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at h₁
    refine Submodule.span_mono (Submonoid.closure_le.2 ?_) h₁
    rintro _ ⟨i', hi', j, rfl⟩
    refine ⟨(Pi.single j 1 : Fin (d + 1) → ℤ) - Pi.single i' 1, by simp, fun l hl => ?_,
      (prod_single_sub x hne i' j).symm⟩
    have hl' : l ≠ i' := fun h => hl (h ▸ hi')
    simp only [Pi.sub_apply, Pi.single_apply, hl', if_false, sub_zero]
    split_ifs <;> omega
  have hP := prod_exp x hne i₀
  have hy' : y = (∏ j, x j ^ ((1 : ℤ) - if j = i₀ then ((d : ℤ) + 1) else 0)) * ((∏ j, x i₀ / x j) * y) := by
    rw [← mul_assoc, hP, one_mul]
  rw [hy']
  generalize (∏ j, x i₀ / x j) * y = z at hz
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, hm, hm', rfl⟩ := hf
    rw [← prod_zpow_add x hne]
    refine hρ.2 _ ?_ ?_
    · rw [Finset.sum_add_distrib, hm, add_zero, Finset.sum_sub_distrib]
      simp
    · intro h0
      have := congrFun h0 i
      simp only [hii₀, if_false, Pi.zero_apply] at this
      have := hm' i hi
      omega
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [mul_smul_comm, map_smul, ha, smul_zero]


end GlobalTheory.PD
