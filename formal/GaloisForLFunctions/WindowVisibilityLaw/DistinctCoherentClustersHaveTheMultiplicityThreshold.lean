import GaloisForLFunctions.WindowVisibilityLaw.CoherentClusterAndTiltAmplificationLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfRightZeros
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# Distinct coherent clusters have the multiplicity threshold

Universal positivity over distinct depth-`δ` clusters in any neighbourhood of
one ordinate has exactly the multiplicity threshold `k * pairEnergy δ a ≤ L`.
A negative test at the coincident cluster persists under a small splitting of
its ordinates, since the finite transform sum is continuous.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.WindowVisibilityLaw

open ArithmeticCastelnuovoSeveri SquareRootThreshold

private def splitOrdinate (k : ℕ) (γ₀ t : ℝ) (j : Fin k) : ℝ := γ₀ + t * j

private theorem injective_splitOrdinate (k : ℕ) (γ₀ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    Function.Injective (splitOrdinate k γ₀ t) := by
  intro i j hij
  have he : (i : ℝ) = j := mul_left_cancel₀ ht (add_left_cancel hij)
  exact Fin.ext (by exact_mod_cast he)

/-- The finite pair sum retains multiplicity when ordinates coincide. -/
private def splitPairForm (k : ℕ) (L δ γ₀ : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  2 * L * (∫ u, f u * conj (f u)) + ∑ j : Fin k,
    (paperFT f ((splitOrdinate k γ₀ t j : ℂ) - I * δ) *
        conj (paperFT f ((splitOrdinate k γ₀ t j : ℂ) + I * δ)) +
      paperFT f ((splitOrdinate k γ₀ t j : ℂ) + I * δ) *
        conj (paperFT f ((splitOrdinate k γ₀ t j : ℂ) - I * δ)))

/-- Above the multiplicity threshold, distinct simple pairs arbitrarily close to
one ordinate are detected by a compact window test. -/
theorem exists_distinct_cluster_negative_of_lt_pairEnergy
    (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hE : L < (k : ℝ) * pairEnergy δ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Fin k → ℝ, Function.Injective γ ∧ (∀ j, |γ j - γ₀| < ε) ∧
      ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((multiPairConfig hL (fun _ => δ) γ (fun _ => hδ) (fun _ => hδ')).W f f).re < 0 := by
  have hnot : ¬ WindowPositiveAt (multiplicityPairConfig k hk hL hδ hδ' γ₀) a := by
    rw [windowPositiveAt_multiplicityPairConfig_iff k hk hL hδ hδ' γ₀ ha haL]
    exact not_le.mpr hE
  unfold WindowPositiveAt at hnot
  push Not at hnot
  obtain ⟨f, hf, hfs, hneg⟩ := hnot
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Icc_subset_Icc (by linarith only [haL]) haL)
  have hfc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  have hft : Continuous (paperFT f) :=
    (_root_.RHTower.EvenSector.differentiable_paperFT_of_compact hf.continuous hfc).continuous
  have hcont : Continuous (fun t : ℝ => (splitPairForm k L δ γ₀ f t).re) := by
    unfold splitPairForm splitOrdinate
    fun_prop
  have hzero : splitPairForm k L δ γ₀ f 0 =
      (multiplicityPairConfig k hk hL hδ hδ' γ₀).W f f := by
    rw [W_multiplicityPairConfig k hk hL hδ hδ' γ₀ hf hfs']
    simp only [splitPairForm, splitOrdinate, zero_mul, add_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hneg₀ : (splitPairForm k L δ γ₀ f 0).re < 0 := by rw [hzero]; exact hneg
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hcont.continuousAt.tendsto.eventually (gt_mem_nhds hneg₀))
  let t : ℝ := min η (ε / ((k : ℝ) + 1)) / 2
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  have hmin : 0 < min η (ε / ((k : ℝ) + 1)) := lt_min hη (div_pos hε hkpos)
  have ht : 0 < t := div_pos hmin (by norm_num)
  have htmin : t < min η (ε / ((k : ℝ) + 1)) := by dsimp only [t]; linarith only [hmin]
  have htη : t < η := htmin.trans_le (min_le_left _ _)
  have htk : t * (k : ℝ) < ε := by
    have h := (lt_div_iff₀ hkpos).mp (htmin.trans_le (min_le_right _ _))
    nlinarith only [h, ht]
  have hinj := injective_splitOrdinate k γ₀ ht.ne'
  have hpoint : Function.Injective fun j : Fin k =>
      offLinePoint δ (splitOrdinate k γ₀ t j) := by
    intro i j hij
    exact hinj (congrArg Complex.im hij)
  refine ⟨splitOrdinate k γ₀ t, hinj, ?_, f, hf, hfs, ?_⟩
  · intro j
    have hj : (j : ℝ) ≤ k := by exact_mod_cast j.isLt.le
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j.val
    calc
      |splitOrdinate k γ₀ t j - γ₀| = t * (j : ℝ) := by
        simp only [splitOrdinate, add_sub_cancel_left, abs_of_nonneg (mul_nonneg ht.le hj0)]
      _ ≤ t * (k : ℝ) := mul_le_mul_of_nonneg_left hj ht.le
      _ < ε := htk
  · rw [W_multiPairConfig hL (fun _ => δ) (splitOrdinate k γ₀ t)
      (fun _ => hδ) (fun _ => hδ') hpoint hf hfs']
    exact hnear (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htη)

/-- The exact multiplicity threshold governs universal positivity of distinct
clusters inside every prescribed neighbourhood of an ordinate. -/
theorem windowPositiveAt_all_distinct_clusters_iff
    (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ γ : Fin k → ℝ, Function.Injective γ → (∀ j, |γ j - γ₀| < ε) →
      WindowPositiveAt (multiPairConfig hL (fun _ => δ) γ
        (fun _ => hδ) (fun _ => hδ')) a) ↔ (k : ℝ) * pairEnergy δ a ≤ L := by
  constructor
  · intro hwp
    by_contra hE
    obtain ⟨γ, hinj, hclose, f, hf, hfs, hneg⟩ :=
      exists_distinct_cluster_negative_of_lt_pairEnergy k hk hL hδ hδ' γ₀ ha haL
        (not_le.mp hE) hε
    exact not_lt_of_ge (hwp γ hinj hclose f hf hfs) hneg
  · intro hE γ hinj _hclose f hf hfs
    have hpoint : Function.Injective fun j : Fin k => offLinePoint δ (γ j) := by
      intro i j hij
      exact hinj (congrArg Complex.im hij)
    have h := re_W_multiPairConfig_ge_of_nodes hL (fun _ => δ) γ (fun _ => hδ)
      (fun _ => hδ') hpoint ∅ ha.le haL hf hfs (by simp)
    have hsum : ∑ j ∈ (∅ : Finset (Fin k))ᶜ, pairEnergy δ a =
        (k : ℝ) * pairEnergy δ a := by simp
    rw [hsum] at h
    exact (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sub_nonneg.mpr hE))
      (integral_nonneg fun u => sq_nonneg ‖f u‖)).trans h

#print axioms exists_distinct_cluster_negative_of_lt_pairEnergy
#print axioms windowPositiveAt_all_distinct_clusters_iff

end GaloisForLFunctions.WindowVisibilityLaw
