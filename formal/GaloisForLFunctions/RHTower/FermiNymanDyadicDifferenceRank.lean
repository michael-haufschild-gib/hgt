import GaloisForLFunctions.RHTower.FermiNymanMultiplicityIndex

/-!
# Exact source rank of the literal Fermi dyadic difference

The difference `w(t/2)-w(t)` is taken on the actual interval `(0,1]`. Every negative
orthonormal witness family has independent differences: a vanishing coefficient difference
would be self-similar and have zero quadratic form, contrary to the negative Gram identity.

Every independent-difference witness family injects into the analytic-multiplicity correlation
coordinates, because a zero coordinate packet forces its difference to vanish. Finite-dimensional
counting, with the infinite-zero case discharged internally, gives the reverse rank bound.
Thus the extended algebraic rank of this literal source difference equals the total right-strip
zeta multiplicity and the dyadic negative index, without RH or finiteness premises.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- The literal source difference on its physical witness interval. -/
def fermiDyadicDifference (w : ℝ → ℂ) : Ioc (0 : ℝ) 1 → ℂ :=
  fun t => w (t / 2) - w t

theorem fermiDyadicDifference_sum {ι : Type*} [Fintype ι]
    (v : ι → ℝ → ℂ) (c : ι → ℂ) :
    fermiDyadicDifference (fun t => ∑ i, c i * v i t) =
      ∑ i, c i • fermiDyadicDifference (v i) := by
  funext t
  simp only [fermiDyadicDifference, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib]

theorem fermiDyadicDifference_eq_zero_iff {w : ℝ → ℂ} :
    fermiDyadicDifference w = 0 ↔ ∀ t ∈ Ioc (0 : ℝ) 1, w (t / 2) = w t := by
  constructor
  · intro h t ht
    have := congrFun h ⟨t, ht⟩
    exact sub_eq_zero.mp this
  · intro h
    funext t
    exact sub_eq_zero.mpr (h t t.2)

theorem dyadicForm_self_eq_zero_of_difference_eq_zero {w : ℝ → ℂ}
    (hD : fermiDyadicDifference w = 0) : dyadicForm w w = 0 := by
  apply dyadicForm_eq_zero_of_selfSimilar
  intro t ht
  rw [fermiDyadicDifference_eq_zero_iff.mp hD t ht]

theorem negative_family_difference_linearIndependent {n : ℕ} (v : Fin n → ℝ → ℂ)
    (hv : ∀ i, IsFermiNymanWitness (v i))
    (hq : ∀ i j, dyadicForm (v i) (v j) = if i = j then -1 else 0) :
    LinearIndependent ℂ (fun i => fermiDyadicDifference (v i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hD : fermiDyadicDifference (fun t => ∑ i, c i * v i t) = 0 := by
    rw [fermiDyadicDifference_sum]
    exact hc
  have h0 := dyadicForm_self_eq_zero_of_difference_eq_zero hD
  rw [dyadicForm_negative_family_sum v hv hq c] at h0
  have hsum : ∑ i, ‖c i‖ ^ 2 = 0 := by
    have h := congrArg Complex.re h0
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.zero_re] at h
    linarith
  have hle : ‖c i‖ ^ 2 ≤ ∑ j, ‖c j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖c j‖) (Finset.mem_univ i)
  rw [hsum] at hle
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (c i)])

def IsIndependentDyadicDifferenceFamily (n : ℕ) : Prop :=
  ∃ v : Fin n → ℝ → ℂ, (∀ i, IsFermiNymanWitness (v i)) ∧
    LinearIndependent ℂ (fun i => fermiDyadicDifference (v i))

/-- Extended algebraic rank of the dyadic difference on actual Fermi witnesses. -/
def witnessDyadicDifferenceRank : ℕ∞ :=
  ⨆ n : ℕ, ⨆ _ : IsIndependentDyadicDifferenceFamily n, (n : ℕ∞)

theorem witnessNegIndex_le_witnessDyadicDifferenceRank :
    witnessNegIndex ≤ witnessDyadicDifferenceRank := by
  refine iSup₂_le fun n hn => ?_
  obtain ⟨v, hv, hq⟩ := hn
  exact le_iSup_of_le n (le_iSup_of_le
    ⟨v, hv, negative_family_difference_linearIndependent v hv hq⟩ le_rfl)

theorem independentDifferenceFamily_card_le_multiplicity [Fintype rightStripZeros]
    {n : ℕ} (hfamily : IsIndependentDyadicDifferenceFamily n) :
    n ≤ ∑ ρ : rightStripZeros, rightStripMultiplicity ρ := by
  classical
  obtain ⟨v, hv, hli⟩ := hfamily
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
    have hJ : fermiMultiplicityJetPacket (fun t => ∑ i, c i * v i t) = 0 := by
      have heq : fermiMultiplicityJetPacket (fun t => ∑ i, c i * v i t) = L c := by
        funext a
        exact fermiCorrelationJet_sum v c hv (by linarith [a.1.2.2.1]) a.2
      exact heq.trans hc
    have hW : IsFermiNymanWitness (fun t => ∑ i, c i * v i t) :=
      isFermiNymanWitness_finsetSum Finset.univ v c (fun i _ => hv i)
    have hD : fermiDyadicDifference (fun t => ∑ i, c i * v i t) = 0 :=
      fermiDyadicDifference_eq_zero_iff.mpr
        (fun t ht => hW.selfSimilar_of_jetPacket_eq_zero hJ ht)
    rw [fermiDyadicDifference_sum] at hD
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hD i
  have hdim := L.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
  simpa only [J, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Fintype.card_sigma, Fintype.card_fin] using hdim

theorem witnessDyadicDifferenceRank_le_rightStripMultiplicityCount :
    witnessDyadicDifferenceRank ≤ rightStripMultiplicityCount := by
  classical
  cases fintypeOrInfinite rightStripZeros with
  | inl h =>
    letI := h
    rw [rightStripMultiplicityCount_eq_sum]
    refine iSup₂_le fun n hn => ?_
    exact_mod_cast independentDifferenceFamily_card_le_multiplicity hn
  | inr h =>
    letI := h
    rw [rightStripMultiplicityCount_eq_top]
    exact le_top

/-- Every analytic zero multiplicity is one independent literal dyadic difference. -/
theorem witnessDyadicDifferenceRank_eq_rightStripMultiplicityCount :
    witnessDyadicDifferenceRank = rightStripMultiplicityCount := by
  apply le_antisymm witnessDyadicDifferenceRank_le_rightStripMultiplicityCount
  rw [← witnessNegIndex_eq_rightStripMultiplicityCount]
  exact witnessNegIndex_le_witnessDyadicDifferenceRank

end RHTower
