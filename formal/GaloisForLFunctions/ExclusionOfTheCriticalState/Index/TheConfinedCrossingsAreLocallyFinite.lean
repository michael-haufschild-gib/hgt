import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConfinedIndexCountsDistinctCriticalRatios
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheConfinedFormHasFiniteIndexAtEveryRatio
import GaloisForLFunctions.HTGeometry.RealQuadraticMargin

/-!
# Local finiteness of the confined crossings

A fixed positive ratio admits only bounded-dimensional negative window families.
Otherwise a negative window direction could be chosen orthogonal to any finite
set of earlier tests, contradicting compactness of the normalized nonpositive cone.
The crossing count then bounds the number of critical ratios in every bounded interval.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations CriticalArithmeticCorrelationTheory
  ArithmeticCastelnuovoSeveri CohomologyOfWindowsOfSpecZ HTGeometry

private theorem coeff_sq_sum_pos {n : ℕ} {t : Fin n → ℝ} (ht : t ≠ 0) : 0 < ∑ i, t i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by by_contra! h; exact ht (funext h)
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- Every strictly negative finite-dimensional space in the actual domain is
realized by a smooth window family of the same dimension and a positive margin. -/
theorem negative_windows_of_strict_domain_family {r : ℝ} (hr : 0 < r) {n : ℕ}
    {G : Fin n → ℝ → ℝ} (hG : ∀ i, CriticalHalfLineEnergyDomain (G i))
    (hg : ∀ t : Fin n → ℝ, t ≠ 0 → criticalHalfLineFullEnergy r (fun u => ∑ i, t i * G i u) < 0) :
    ∃ (H : Fin n → ℝ → ℝ) (δ : ℝ), (∀ i, IsHalfLineTest (H i)) ∧ 0 < δ ∧
      ∀ t : Fin n → ℝ, criticalHalfLineFullEnergy r (fun u => ∑ i, t i * H i u) ≤
        -(δ * ∑ i, t i ^ 2) := by
  classical
  let m := fun i => ∫ u, G i u ^ 2
  let k := fun i => (Real.sqrt (max 1 (m i)))⁻¹
  let Y := fun i u => k i * G i u
  have hp (i) : 0 < max 1 (m i) := one_pos.trans_le (le_max_left _ _)
  have hk (i) : 0 < k i := inv_pos.mpr (Real.sqrt_pos.mpr (hp i))
  have hY (i) : CriticalHalfLineEnergyDomain (Y i) := (hG i).const_mul _
  have hmass (i) : (∫ u, Y i u ^ 2) ≤ 1 := by
    simp only [Y, mul_pow, integral_const_mul, k, inv_pow, Real.sq_sqrt (hp i).le]
    change (max 1 (m i))⁻¹ * m i ≤ 1
    rw [← div_eq_inv_mul, div_le_one (hp i)]
    exact le_max_right _ _
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => criticalHalfLineMixedEnergy r (Y i) (Y j)
  have hQ (t : Fin n → ℝ) : realQuad A t = criticalHalfLineFullEnergy r (fun u => ∑ i, t i * Y i u) := by
    rw [fullEnergy_finsetSum_eq r _ hY t]
    unfold realQuad A
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hneg (t : Fin n → ℝ) (ht : t ≠ 0) : realQuad A t < 0 := by
    rw [hQ]
    have hn : (fun i => t i * k i) ≠ 0 := by
      intro h; apply ht; funext i
      exact (mul_eq_zero.mp (congrFun h i)).resolve_right (hk i).ne'
    simpa only [Y, mul_assoc] using hg _ hn
  obtain ⟨η, hη, hbound⟩ := exists_margin_of_negDef A hneg
  let δ := η / ((n : ℝ) + 1)
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hb (t : Fin n → ℝ) : ∑ i, t i ^ 2 ≤ ((n : ℝ)+1) * ‖t‖ ^ 2 := by
    calc ∑ i, t i ^ 2 ≤ ∑ _i : Fin n, ‖t‖ ^ 2 := by
           apply Finset.sum_le_sum; intro i _
           have h := norm_le_pi_norm t i
           rw [Real.norm_eq_abs] at h
           simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (t i)) h 2
         _ ≤ ((n : ℝ)+1) * ‖t‖ ^ 2 := by
           simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
           linarith only [sq_nonneg ‖t‖]
  have hrec (t : Fin n → ℝ) : criticalHalfLineFullEnergy r (fun u => ∑ i, t i * Y i u) ≤
      -(δ * ∑ i, t i ^ 2) := by
    rw [← hQ]
    have e : δ * ((n : ℝ)+1) = η := div_mul_cancel₀ _ (by positivity)
    have h := mul_le_mul_of_nonneg_left (hb t) hδ.le
    rw [← mul_assoc, e] at h
    linarith only [hbound t, h]
  obtain ⟨H, hw, hH⟩ := exists_window_family_of_negative hr hY hmass hδ hrec
  refine ⟨H, δ/2, fun i => ?_, half_pos hδ, hH⟩
  obtain ⟨A, -, hA⟩ := hw i
  exact ⟨hA.1, A, hA.2⟩

private theorem unit_negative_orthogonal_to_tests {r : ℝ} (hr : 0 < r) {n : ℕ} {H : Fin n → ℝ → ℝ}
    (hH : ∀ i, IsHalfLineTest (H i))
    (hneg : ∀ t : Fin n → ℝ, t ≠ 0 → criticalHalfLineFullEnergy r (fun u => ∑ i, t i * H i u) < 0)
    (s : Finset (ℝ → ℝ)) (hs : ∀ f ∈ s, NonpositiveUnitTest r f) (hcard : s.card < n) :
    ∃ U, NonpositiveUnitTest r U ∧ ∀ f ∈ s, (∫ u, f u * U u) = 0 := by
  classical
  let M := fun (j : s) (i : Fin n) => ∫ u, j.val u * H i u
  let L : (Fin n → ℝ) →ₗ[ℝ] (s → ℝ) :=
    { toFun := fun t j => ∑ i, t i * M j i
      map_add' := fun v w => by funext j; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a t => by
        funext j; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hk : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hcard
  obtain ⟨t, hker, ht⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  let X := fun u => ∑ i, t i * H i u
  obtain ⟨A, hA⟩ := exists_common_window hH
  have hwin : IsWindowTest A X := isWindowTest_finsetSum _ (fun i => ⟨(hH i).1, hA i⟩) t
  have hX := criticalHalfLineEnergyDomain_of_window hwin
  have he := hneg t ht
  have hm : 0 < ∫ u, X u ^ 2 := integral_sq_pos_of_fullEnergy_neg hr hX he
  let k := (Real.sqrt (∫ u, X u ^ 2))⁻¹
  have hp : 0 < k := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  have hnorm : (∫ u, (k * X u) ^ 2) = 1 := by
    simp only [mul_pow, integral_const_mul, k, inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  refine ⟨fun u => k * X u, ⟨contDiff_const.mul hwin.contDiff, hwin.hasCompactSupport.mul_left (f := fun _ => k),
    fun u hu => by change k * X u = 0; rw [hX.support u hu, mul_zero], hnorm, ?_⟩, ?_⟩
  · rw [criticalHalfLineFullEnergy_const_mul]
    exact (mul_neg_of_pos_of_neg (sq_pos_of_pos hp) he).le
  · intro f hf
    have hfi (i : Fin n) : Integrable (fun u => f u * H i u) :=
      ((hs f hf).1.continuous.mul (hH i).1.continuous).integrable_of_hasCompactSupport
        ((hs f hf).2.1.mul_right)
    have eqn : (fun u => f u * (k * X u)) =
        fun u => k * ∑ i, t i * (f u * H i u) := by
      funext u
      simp only [X, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [eqn, integral_const_mul, integral_finsetSum _ fun i _ => (hfi i).const_mul (t i)]
    simp only [integral_const_mul]
    have hv := congrFun (LinearMap.mem_ker.mp hker) (⟨f,hf⟩ : s)
    change ∑ i, t i * (∫ u, f u * H i u) = 0 at hv
    rw [hv, mul_zero]

/-- At each positive ratio one bound works for every negative real window
family, including families with arbitrarily large supports. -/
theorem exists_bound_negative_window_families {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ (n : ℕ) (H : Fin n → ℝ → ℝ), (∀ i, IsHalfLineTest (H i)) →
      (∀ t : Fin n → ℝ, t ≠ 0 → criticalHalfLineFullEnergy r (fun u => ∑ i, t i * H i u) < 0) → n ≤ N := by
  classical
  by_contra! h
  have step (s : Finset (ℝ → ℝ)) (hs : ∀ f ∈ s, NonpositiveUnitTest r f) :
      ∃ U, NonpositiveUnitTest r U ∧ ∀ f ∈ s, (∫ u, f u * U u) = 0 := by
    obtain ⟨n, H, hH, hneg, hn⟩ := h s.card
    exact unit_negative_orthogonal_to_tests hr hH hneg s hs hn
  obtain ⟨f, hf, ho⟩ := exists_seq_of_forall_finset_exists (NonpositiveUnitTest r)
    (fun f g => (∫ u, f u * g u) = 0) step
  obtain ⟨N, hN⟩ := exists_bound_orthonormal_nonpositive hr
  have hn := hN (N+1) (fun i => f i.val) (fun i => hf _) (fun i j hij => by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ho _ _ hlt
    · simpa only [mul_comm] using ho _ _ hgt)
  omega

/-- For each fixed positive ratio the negative Hermitian indices of all smooth
half-line families have a uniform finite bound. -/
theorem windowIndicesAt_bddAbove {r : ℝ} (hr : 0 < r) : BddAbove (windowIndicesAt r) := by
  obtain ⟨N,hN⟩ := exists_bound_negative_window_families hr
  refine ⟨N, ?_⟩
  rintro n ⟨S,H,hH,hn⟩
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    obtain ⟨s,hs,h⟩ := (confined_index_at_ratio_iff_distinct_critical_ratios n hr).mp
      ⟨S,H,hH,hn.le⟩
    obtain ⟨G,δ,hG,hδ,hneg⟩ := negative_window_family_of_distinct_critical_ratios hr hs.injective
      (fun i => (h i).1) (fun i => (h i).2.1) (fun i => (h i).2.2)
    exact hN _ G hG (fun t ht => (hneg t).trans_lt (neg_lt_zero.mpr (mul_pos hδ (coeff_sq_sum_pos ht))))

/-- Only finitely many positive critical ratios lie below any finite bound. -/
theorem finite_critical_ratios_below (b : ℝ) :
    {r : ℝ | 0 < r ∧ r ≤ b ∧ ∃ F, IsConfinedNullVector r F}.Finite := by
  classical
  let u := max 1 (b+1)
  have hu : 0 < u := one_pos.trans_le (le_max_left _ _)
  have hbu : b < u := (lt_add_one b).trans_le (le_max_right _ _)
  obtain ⟨N,hN⟩ := windowIndicesAt_bddAbove hu
  by_contra hinf
  obtain ⟨s,hs,hc⟩ := Set.Infinite.exists_subset_card_eq hinf (N+1)
  let e := (finCongr hc.symm).trans s.equivFin.symm
  let x := fun i : Fin (N+1) => (e i).val
  obtain ⟨S,H,hH,hindex⟩ := window_index_of_distinct_critical_ratios hu
    (s := x) (Subtype.val_injective.comp e.injective)
    (fun i => (hs (e i).property).1) (fun i => (hs (e i).property).2.1.trans_lt hbu)
    (fun i => (hs (e i).property).2.2)
  have hcap := hN (show hermNegIndex (confinedGram u H) ∈ windowIndicesAt u from ⟨S,H,hH,rfl⟩)
  omega

#print axioms negative_windows_of_strict_domain_family
#print axioms windowIndicesAt_bddAbove
#print axioms finite_critical_ratios_below
end GaloisForLFunctions.ExclusionOfTheCriticalState
