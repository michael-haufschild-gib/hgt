import GaloisForLFunctions.ArithmeticOrientationTheory.FiniteWienerJetsCanBePrescribed

/-!
# Interior jets and boundary values can be prescribed

Masks vanishing to all prescribed interior orders allow independent
correction of finitely many additional closed-half-plane values.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

/-- A finite interior jet mask can avoid any other point of the closed half-plane. -/
theorem exists_wiener_jet_mask_avoiding
    {ι : Type} [Fintype ι] (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re)
    (m : ι → ℕ) (t : ℂ) (ht : (1 / 2 : ℝ) ≤ t.re) (hne : ∀ i, t ≠ s i) :
    ∃ a : WienerAlgebraAt (1 / 2), LSeries (⇑a.toFn) t ≠ 0 ∧
      ∀ i, (m i : ℕ∞) ≤ analyticOrderAt (LSeries (⇑a.toFn)) (s i) := by
  classical
  let χ := WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) t ht)
  let ψ (i : ι) := WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) (s i) (hs i).le)
  have hsep (i : ι) : ∃ a : WienerAlgebraAt (1 / 2), χ a ≠ ψ i a :=
    halfPlane_characters_separated ht (hs i).le (hne i)
  choose a ha using hsep
  let b (i : ι) := a i - algebraMap ℂ (WienerAlgebraAt (1 / 2)) (ψ i (a i))
  let M : WienerAlgebraAt (1 / 2) := ∏ i, b i ^ m i
  refine ⟨M, ?_, fun i => ?_⟩
  · rw [wienerLSeries_eq_character _ ht]
    change χ (∏ i, b i ^ m i) ≠ 0
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [map_pow]
    apply pow_ne_zero
    change χ (a i - algebraMap ℂ (WienerAlgebraAt (1 / 2)) (ψ i (a i))) ≠ 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply]
    exact sub_ne_zero.mpr (ha i)
  · have hzero : LSeries (⇑(b i).toFn) (s i) = 0 := by
      rw [wienerLSeries_eq_character _ (hs i).le]
      change ψ i (a i - algebraMap ℂ (WienerAlgebraAt (1 / 2)) (ψ i (a i))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have h1 := one_le_wiener_order_of_zero (b i) (hs i) hzero
    have hn : (m i : ℕ∞) ≤ (m i) • analyticOrderAt (LSeries (⇑(b i).toFn)) (s i) := by
      calc
        (m i : ℕ∞) = (m i) • (1 : ℕ∞) := by simp
        _ ≤ _ := by gcongr
    have hdiv : b i ^ m i ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨r, hr⟩ := hdiv
    rw [hr, analyticOrderAt_wiener_mul _ _ (hs i), analyticOrderAt_wiener_pow _ (hs i)]
    exact hn.trans le_self_add

/-- Interior jets and distinct additional closed-half-plane values can be prescribed jointly. -/
theorem exists_wiener_with_mixed_finite_data
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) (hsinj : Function.Injective s)
    (m : ι → ℕ) (v : ι → ℕ → ℂ)
    (t : β → ℂ) (ht : ∀ j, (1 / 2 : ℝ) ≤ (t j).re) (htinj : Function.Injective t)
    (hdisj : ∀ i j, s i ≠ t j) (w : β → ℂ) :
    ∃ a : WienerAlgebraAt (1 / 2),
      (∀ i k, k < m i → iteratedDeriv k (LSeries (⇑a.toFn)) (s i) = v i k) ∧
      (∀ j, LSeries (⇑a.toFn) (t j) = w j) := by
  classical
  obtain ⟨a, ha⟩ := exists_wiener_with_prescribed_finite_jets s hs hsinj m v
  let χ (j : β) := WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) (t j) (ht j))
  have hsep (j k : β) (hjk : j ≠ k) : ∃ b : WienerAlgebraAt (1 / 2), χ j b ≠ χ k b :=
    halfPlane_characters_separated (ht j) (ht k) (fun h => hjk (htinj h))
  have he (j : β) : ∃ e : WienerAlgebraAt (1 / 2),
      ∀ k, χ k e = if k = j then 1 else 0 := by
    obtain ⟨e, he⟩ := surjective_pi_algHom_of_separated χ hsep (fun k => if k = j then 1 else 0)
    exact ⟨e, fun k => congrFun he k⟩
  choose e he using he
  have hmask (j : β) : ∃ b : WienerAlgebraAt (1 / 2),
      LSeries (⇑b.toFn) (t j) ≠ 0 ∧
        ∀ i, (m i : ℕ∞) ≤ analyticOrderAt (LSeries (⇑b.toFn)) (s i) :=
    exists_wiener_jet_mask_avoiding s hs m (t j) (ht j) (fun i => (hdisj i j).symm)
  choose b hbnonzero hborder using hmask
  have hb (j : β) : χ j (b j) ≠ 0 := by
    simpa only [wienerLSeries_eq_character _ (ht j)] using hbnonzero j
  -- Normalize the masked value selectors without changing any interior jet.
  let B (j : β) : WienerAlgebraAt (1 / 2) := (χ j (b j))⁻¹ • (b j * e j)
  have hBvalue (j k : β) : χ k (B j) = if k = j then 1 else 0 := by
    simp only [B, map_smul, map_mul, smul_eq_mul, he]
    by_cases h : k = j
    · subst k
      rw [if_pos rfl, mul_one, inv_mul_cancel₀ (hb j)]
    · rw [if_neg h, mul_zero, mul_zero]
  have hBjet (i : ι) (k : ℕ) (hk : k < m i) (j : β) :
      wienerJetLinear (s i) (hs i) k (B j) = 0 := by
    have hord : (m i : ℕ∞) ≤ analyticOrderAt (LSeries (⇑(b j * e j).toFn)) (s i) := by
      rw [analyticOrderAt_wiener_mul _ _ (hs i)]
      exact (hborder j i).trans le_self_add
    have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_wienerLSeries (b j * e j) (hs i))).mp hord k hk
    change wienerJetLinear (s i) (hs i) k ((χ j (b j))⁻¹ • (b j * e j)) = 0
    rw [map_smul]
    change (χ j (b j))⁻¹ * iteratedDeriv k (LSeries (⇑(b j * e j).toFn)) (s i) = 0
    rw [hz, mul_zero]
  refine ⟨a + ∑ j, (w j - χ j a) • B j, ?_, ?_⟩
  · intro i k hk
    change wienerJetLinear (s i) (hs i) k (a + ∑ j, (w j - χ j a) • B j) = v i k
    rw [map_add, map_sum]
    simp only [map_smul, hBjet i k hk, smul_zero, sum_const_zero, add_zero]
    exact ha i k hk
  · intro j
    rw [wienerLSeries_eq_character _ (ht j)]
    change χ j (a + ∑ k, (w k - χ k a) • B k) = w j
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hBvalue]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_one]
      ring
    · intro k _ hkj
      rw [if_neg hkj.symm, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ j))

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_wiener_jet_mask_avoiding
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_wiener_with_mixed_finite_data
end
