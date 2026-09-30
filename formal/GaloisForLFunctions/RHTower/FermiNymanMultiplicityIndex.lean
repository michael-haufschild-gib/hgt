import GaloisForLFunctions.RHTower.FermiNymanCorrelationJets

/-!
# Exact multiplicity index of the literal Fermi witness form

Conjugated correlation-Mellin jets give complex-linear coordinates indexed by every analytic
multiplicity slot of every actual right-strip zeta zero. A witness with zero coordinate packet is
self-similar by local pole cancellation, hence has zero dyadic quadratic form. Consequently the
coordinate map is injective on every negative orthonormal witness span.

For a finite right-strip zero set, finite-dimensional linear algebra bounds each negative family
by the sum of analytic multiplicities. For an infinite zero set, that extended-natural sum is top.
Together with the literal hyperbolic blocks, this proves the unconditional exact index formula.
No zero simplicity, finiteness, Riemann hypothesis, or source positivity is assumed.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- Every right-strip multiplicity slot reads a conjugated correlation-Mellin jet. -/
def fermiMultiplicityJetPacket (w : ℝ → ℂ) :
    (Σ ρ : rightStripZeros, Fin (rightStripMultiplicity ρ)) → ℂ :=
  fun a => fermiCorrelationJet w a.1 a.2

theorem IsFermiNymanWitness.selfSimilar_of_jetPacket_eq_zero {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) (hJ : fermiMultiplicityJetPacket w = 0)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  apply hw.selfSimilar_of_correlation_order ?_ ht
  intro ρ
  rw [← rightStripMultiplicity_coe ρ]
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hw.analyticAt_fermiCorrelation (by linarith [ρ.2.2.1]))).mpr
  intro j hj
  have h := congrFun hJ ⟨ρ, ⟨j, hj⟩⟩
  have h' := congrArg (starRingEnd ℂ) h
  simpa [fermiMultiplicityJetPacket, fermiCorrelationJet] using h'

theorem dyadicForm_self_eq_zero_of_jetPacket_eq_zero {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) (hJ : fermiMultiplicityJetPacket w = 0) :
    dyadicForm w w = 0 := by
  rw [dyadicForm_self, integral_half_normSq_of_selfSimilar
    (fun t ht => hw.selfSimilar_of_jetPacket_eq_zero hJ ht)]
  simp

theorem dyadicForm_negative_family_sum {n : ℕ} (v : Fin n → ℝ → ℂ)
    (hv : ∀ i, IsFermiNymanWitness (v i))
    (hq : ∀ i j, dyadicForm (v i) (v j) = if i = j then -1 else 0) (c : Fin n → ℂ) :
    dyadicForm (fun t => ∑ i, c i * v i t) (fun t => ∑ i, c i * v i t) =
      -((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
  rw [dyadicForm_sum_sum v c c (fun i j => (hv i).integrableOn_mul_conj_witness (hv j))]
  simp only [hq, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.sum_neg_distrib]
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_sum]

theorem coefficients_eq_zero_of_negative_family_jetPacket_eq_zero {n : ℕ}
    (v : Fin n → ℝ → ℂ) (hv : ∀ i, IsFermiNymanWitness (v i))
    (hq : ∀ i j, dyadicForm (v i) (v j) = if i = j then -1 else 0) (c : Fin n → ℂ)
    (hc : fermiMultiplicityJetPacket (fun t => ∑ i, c i * v i t) = 0) : c = 0 := by
  have hW : IsFermiNymanWitness (fun t => ∑ i, c i * v i t) :=
    isFermiNymanWitness_finsetSum Finset.univ v c (fun i _ => hv i)
  have h0 := dyadicForm_self_eq_zero_of_jetPacket_eq_zero hW hc
  rw [dyadicForm_negative_family_sum v hv hq c] at h0
  have hsum : ∑ i, ‖c i‖ ^ 2 = 0 := by
    have h := congrArg Complex.re h0
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.zero_re] at h
    linarith
  funext i
  have hle : ‖c i‖ ^ 2 ≤ ∑ j, ‖c j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖c j‖) (Finset.mem_univ i)
  rw [hsum] at hle
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (c i)])

theorem negOrthonormalFamily_card_le_multiplicity [Fintype rightStripZeros] {n : ℕ}
    (hfamily : IsNegOrthonormalWitnessFamily n) :
    n ≤ ∑ ρ : rightStripZeros, rightStripMultiplicity ρ := by
  classical
  obtain ⟨v, hv, hq⟩ := hfamily
  let J := Σ ρ : rightStripZeros, Fin (rightStripMultiplicity ρ)
  let L : (Fin n → ℂ) →ₗ[ℂ] (J → ℂ) :=
    { toFun := fun c a => ∑ i, c i * fermiMultiplicityJetPacket (v i) a
      map_add' := by
        intro c d
        funext a
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
          RingHom.id_apply] }
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply coefficients_eq_zero_of_negative_family_jetPacket_eq_zero v hv hq c
    have hJ : fermiMultiplicityJetPacket (fun t => ∑ i, c i * v i t) = L c := by
      funext a
      exact fermiCorrelationJet_sum v c hv (by linarith [a.1.2.2.1]) a.2
    exact hJ.trans hc
  have hdim := L.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
  simpa only [J, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_sigma,
    Fintype.card_fin] using hdim

theorem rightStripMultiplicity_pos (ρ : rightStripZeros) : 0 < rightStripMultiplicity ρ := by
  have hne : (ρ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith [ρ.2.2.2]
  have horder : analyticOrderAt riemannZeta (ρ : ℂ) ≠ 0 :=
    (analyticOn_riemannZeta (ρ : ℂ) hne).analyticOrderAt_ne_zero.mpr ρ.2.1
  apply Nat.pos_of_ne_zero
  intro hm
  apply horder
  rw [← rightStripMultiplicity_coe ρ, hm]
  rfl

theorem rightStripMultiplicityCount_eq_sum [Fintype rightStripZeros] :
    rightStripMultiplicityCount = ((∑ ρ : rightStripZeros, rightStripMultiplicity ρ : ℕ) : ℕ∞) := by
  classical
  apply le_antisymm
  · refine iSup_le fun s => ?_
    exact_mod_cast (Finset.sum_le_sum_of_subset (Finset.subset_univ s) :
      ∑ ρ ∈ s, rightStripMultiplicity ρ ≤ ∑ ρ : rightStripZeros, rightStripMultiplicity ρ)
  · exact le_iSup_of_le (Finset.univ : Finset rightStripZeros) le_rfl

theorem rightStripMultiplicityCount_eq_top [Infinite rightStripZeros] :
    rightStripMultiplicityCount = ⊤ := by
  classical
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  obtain ⟨s, hcard⟩ := Finset.exists_card_eq (α := rightStripZeros) n
  have hs : s.card ≤ ∑ ρ ∈ s, rightStripMultiplicity ρ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun ρ _ => Nat.succ_le_of_lt (rightStripMultiplicity_pos ρ))
  calc
    (n : ℕ∞) = (s.card : ℕ∞) := by rw [hcard]
    _ ≤ ((∑ ρ ∈ s, rightStripMultiplicity ρ : ℕ) : ℕ∞) := by exact_mod_cast hs
    _ ≤ rightStripMultiplicityCount := le_iSup_of_le s le_rfl

theorem witnessNegIndex_le_rightStripMultiplicityCount :
    witnessNegIndex ≤ rightStripMultiplicityCount := by
  classical
  cases fintypeOrInfinite rightStripZeros with
  | inl h =>
    letI := h
    rw [rightStripMultiplicityCount_eq_sum]
    refine iSup₂_le fun n hn => ?_
    exact_mod_cast negOrthonormalFamily_card_le_multiplicity hn
  | inr h =>
    letI := h
    rw [rightStripMultiplicityCount_eq_top]
    exact le_top

/-- The literal dyadic negative index counts all right-strip zeta zero multiplicities exactly. -/
theorem witnessNegIndex_eq_rightStripMultiplicityCount :
    witnessNegIndex = rightStripMultiplicityCount :=
  le_antisymm witnessNegIndex_le_rightStripMultiplicityCount
    rightStripMultiplicityCount_le_witnessNegIndex

end RHTower
