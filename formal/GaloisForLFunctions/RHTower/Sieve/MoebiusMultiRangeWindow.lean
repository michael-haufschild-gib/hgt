import GaloisForLFunctions.RHTower.Sieve.MoebiusTwoRangeWindow
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockPowerCofactorMeanSquare

/-!
# The Möbius window over a ladder of prime ranges

Let ranges `j < J` carry designated primes `P_j`, geometric ladders `(R_j, η_j, L_j)` and block
thresholds `V_{j,v}`.  A frequency belongs to the **first-small set** `T_j` if every block of the
`j`-th range is at most its threshold there, but for every earlier range some block exceeds its
threshold.  The sets `T_j` are disjoint, and their union is the set where some range is all
small.  On `T_j` the Ramaré decomposition at the `j`-th range applies with the pointwise block
bounds; for `j ≥ 1` the cofactor's mean square over `T_j` is paid by amplifying with a large block
of the previous range:

`∫_{T_j} ‖C‖² ≤ ∑_r V_{j-1,r}^{-2ℓ} ∫_{|w| ≤ W} ‖Q_{j-1,r}^ℓ C‖²`.

The complement (outside the disc) is the exceptional set of the two-range argument, taken at the
union of the all-small sets.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- **Union bound for set integrals over a finite cover inside a window.** -/
theorem setIntegral_le_sum_of_subset_biUnion {ι : Type*} (s : Finset ι) {E : Set ℝ}
    {S : ι → Set ℝ} {f : ℝ → ℝ} (hf : Continuous f) {W : ℝ}
    (hS : ∀ i ∈ s, S i ⊆ Set.Icc (-W) W) (hcover : E ⊆ ⋃ i ∈ s, S i) (hnn : ∀ t, 0 ≤ f t) :
    (∫ t in E, f t) ≤ ∑ i ∈ s, ∫ t in S i, f t := by
  classical
  have hfull : IntegrableOn f (Set.Icc (-W) W) volume := hf.integrableOn_Icc
  change Integrable f (volume.restrict (Set.Icc (-W) W)) at hfull
  have hfi : ∀ i : s, Integrable f (volume.restrict (S i)) := fun i =>
    hfull.mono_measure (Measure.restrict_mono (hS i i.2) le_rfl)
  have hsummable : Summable (fun i : s => ∫ t, ‖f t‖ ∂volume.restrict (S i)) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  have hsumInt : Integrable f (Measure.sum fun i : s => volume.restrict (S i)) :=
    integrable_sum_measure hfi hsummable
  have hcover' : E ⊆ ⋃ i : s, S i := by
    intro t ht
    obtain ⟨i, hi, hti⟩ := Set.mem_iUnion₂.mp (hcover ht)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hti⟩
  have hμ : volume.restrict E ≤ Measure.sum (fun i : s => volume.restrict (S i)) :=
    (Measure.restrict_mono hcover' le_rfl).trans Measure.restrict_iUnion_le
  have hmono := integral_mono_measure hμ (Filter.Eventually.of_forall hnn) hsumInt
  rw [integral_sum_measure hsumInt, tsum_fintype] at hmono
  refine hmono.trans (le_of_eq ?_)
  exact Finset.sum_coe_sort s fun i => ∫ t in S i, f t

/-- The all-small set of the `j`-th range. -/
def rangeAllSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ) (V : ℕ → ℕ → ℝ) (W : ℝ)
    (j : ℕ) : Set ℝ :=
  allBlocksSmall (P j) (R j) (η j) (L j) (V j) W

/-- The first-small set of the `j`-th range: all its blocks small, some block of every earlier
range large. -/
def rangeFirstSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ) (V : ℕ → ℕ → ℝ) (W : ℝ)
    (j : ℕ) : Set ℝ :=
  rangeAllSmall P R η L V W j \ ⋃ i ∈ Finset.range j, rangeAllSmall P R η L V W i

/-- The union of the all-small sets below `J`. -/
def rangeUnionSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ) (V : ℕ → ℕ → ℝ) (W : ℝ)
    (J : ℕ) : Set ℝ :=
  ⋃ j ∈ Finset.range J, rangeAllSmall P R η L V W j

theorem measurableSet_rangeAllSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W : ℝ) (j : ℕ) : MeasurableSet (rangeAllSmall P R η L V W j) :=
  measurableSet_allBlocksSmall _ _ _ _ _ _

theorem measurableSet_rangeFirstSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W : ℝ) (j : ℕ) : MeasurableSet (rangeFirstSmall P R η L V W j) :=
  (measurableSet_rangeAllSmall P R η L V W j).diff
    (Finset.measurableSet_biUnion _ fun i _ => measurableSet_rangeAllSmall P R η L V W i)

theorem measurableSet_rangeUnionSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W : ℝ) (J : ℕ) : MeasurableSet (rangeUnionSmall P R η L V W J) :=
  Finset.measurableSet_biUnion _ fun i _ => measurableSet_rangeAllSmall P R η L V W i

theorem rangeAllSmall_subset (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W : ℝ) (j : ℕ) : rangeAllSmall P R η L V W j ⊆ Set.Icc (-W) W :=
  allBlocksSmall_subset _ _ _ _ _ _

theorem rangeFirstSmall_subset (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W : ℝ) (j : ℕ) :
    rangeFirstSmall P R η L V W j ⊆ rangeAllSmall P R η L V W j :=
  Set.sdiff_subset

theorem rangeUnionSmall_subset (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W : ℝ) (J : ℕ) : rangeUnionSmall P R η L V W J ⊆ Set.Icc (-W) W :=
  Set.iUnion₂_subset fun j _ => rangeAllSmall_subset P R η L V W j

/-- Every frequency where some range is all small lies in the first-small set of the least such
range. -/
theorem rangeUnionSmall_subset_biUnion_firstSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ)
    (L : ℕ → ℕ) (V : ℕ → ℕ → ℝ) (W : ℝ) (J : ℕ) :
    rangeUnionSmall P R η L V W J ⊆ ⋃ j ∈ Finset.range J, rangeFirstSmall P R η L V W j := by
  classical
  intro w hw
  obtain ⟨j, hjJ, hjw⟩ := Set.mem_iUnion₂.mp hw
  let S : Finset ℕ := (Finset.range J).filter fun i => w ∈ rangeAllSmall P R η L V W i
  have hSne : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hjJ, hjw⟩⟩
  set i₀ := S.min' hSne with hi₀
  have hi₀S := Finset.min'_mem S hSne
  obtain ⟨hi₀J, hi₀w⟩ := Finset.mem_filter.mp hi₀S
  refine Set.mem_iUnion₂.mpr ⟨i₀, hi₀J, hi₀w, ?_⟩
  intro hmem
  obtain ⟨i, hi, hiw⟩ := Set.mem_iUnion₂.mp hmem
  have hiJ : i ∈ Finset.range J :=
    Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans (Finset.mem_range.mp hi₀J))
  have hle : i₀ ≤ i := Finset.min'_le S i (Finset.mem_filter.mpr ⟨hiJ, hiw⟩)
  exact absurd (Finset.mem_range.mp hi) (not_lt.mpr hle)

/-- On the first-small set of a range `j ≥ 1`, some block of the previous range is large. -/
theorem rangeFirstSmall_subset_someBlockLarge (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W : ℝ) (j : ℕ) :
    rangeFirstSmall P R η L V W (j + 1)
      ⊆ ⋃ r ∈ Finset.range (L j), shortExceptional (geomBlock (P j) (R j) (1 + η j) r) W (V j r) := by
  intro w hw
  obtain ⟨hsmall, hnot⟩ := hw
  have hwI : w ∈ Set.Icc (-W) W := rangeAllSmall_subset P R η L V W (j + 1) hsmall
  have hnj : w ∉ rangeAllSmall P R η L V W j := fun h =>
    hnot (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), h⟩)
  by_contra hcon
  refine hnj ⟨hwI, ?_⟩
  refine Set.mem_iInter₂.mpr fun r hr => ?_
  by_contra hlarge
  simp only [Set.mem_setOf_eq, not_le] at hlarge
  exact hcon (Set.mem_iUnion₂.mpr ⟨r, hr, hwI, hlarge.le⟩)

/-- **The small half of the annulus, split by first-small ranges.** -/
theorem setIntegral_annulusSmall_le_sum_firstSmall (P : ℕ → Finset ℕ) (R η : ℕ → ℝ)
    (L : ℕ → ℕ) (V : ℕ → ℕ → ℝ) (W w₀ : ℝ) (J : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ t, 0 ≤ f t) :
    (∫ w in annulusSmall (rangeUnionSmall P R η L V W J) w₀, f w)
      ≤ ∑ j ∈ Finset.range J, ∫ w in rangeFirstSmall P R η L V W j, f w :=
  setIntegral_le_sum_of_subset_biUnion (Finset.range J) hf
    (fun j _ => (rangeFirstSmall_subset P R η L V W j).trans (rangeAllSmall_subset P R η L V W j))
    (Set.sdiff_subset.trans (rangeUnionSmall_subset_biUnion_firstSmall P R η L V W J)) hnn

/-- **Amplification by a large block.**  On the exceptional set of a block `B` at level `V > 0`,
`‖g‖² ≤ V^{-2ℓ}‖Q_B^ℓ g‖²`; hence over any set covered by exceptional sets
`∫_E ‖g‖² ≤ ∑_r V_r^{-2ℓ_r} ∫_{|w| ≤ W} ‖Q_{B_r}^{ℓ_r} g‖²`. -/
theorem setIntegral_normSq_le_sum_amplified {ι : Type*} (s : Finset ι) {g : ℝ → ℂ}
    (hg : Continuous g) (B : ι → Finset ℕ) (V : ι → ℝ) (hV : ∀ r ∈ s, 0 < V r) (ℓ : ι → ℕ)
    {W : ℝ} {E : Set ℝ} (hE : E ⊆ ⋃ r ∈ s, shortExceptional (B r) W (V r)) :
    (∫ w in E, ‖g w‖ ^ (2 : ℕ))
      ≤ ∑ r ∈ s, (V r ^ (2 * ℓ r))⁻¹
          * ∫ w in Set.Icc (-W) W, ‖primeBlockPoly (B r) w ^ ℓ r * g w‖ ^ (2 : ℕ) := by
  have hcont : Continuous fun w => ‖g w‖ ^ (2 : ℕ) := hg.norm.pow 2
  refine (setIntegral_le_sum_of_subset_biUnion s hcont
    (fun r _ => shortExceptional_subset (B r) W (V r)) hE fun t => by positivity).trans ?_
  refine Finset.sum_le_sum fun r hr => ?_
  have hVr := hV r hr
  have hVpow : 0 < V r ^ (2 * ℓ r) := pow_pos hVr _
  have hcontP : Continuous fun w => ‖primeBlockPoly (B r) w ^ ℓ r * g w‖ ^ (2 : ℕ) :=
    (((continuous_primeBlockPoly (B r)).pow (ℓ r)).mul hg).norm.pow 2
  have hpt : ∀ w ∈ shortExceptional (B r) W (V r), ‖g w‖ ^ (2 : ℕ)
      ≤ (V r ^ (2 * ℓ r))⁻¹ * ‖primeBlockPoly (B r) w ^ ℓ r * g w‖ ^ (2 : ℕ) := by
    intro w hw
    have hVle : V r ≤ ‖primeBlockPoly (B r) w‖ := hw.2
    rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm (ℓ r) 2, le_inv_mul_iff₀ hVpow]
    have hpow : V r ^ (2 * ℓ r) ≤ ‖primeBlockPoly (B r) w‖ ^ (2 * ℓ r) :=
      pow_le_pow_left₀ hVr.le hVle _
    exact mul_le_mul_of_nonneg_right hpow (by positivity)
  have hmeas := measurableSet_shortExceptional (B r) W (V r)
  calc (∫ w in shortExceptional (B r) W (V r), ‖g w‖ ^ (2 : ℕ))
      ≤ ∫ w in shortExceptional (B r) W (V r),
          (V r ^ (2 * ℓ r))⁻¹ * ‖primeBlockPoly (B r) w ^ ℓ r * g w‖ ^ (2 : ℕ) :=
        setIntegral_mono_on
          (hcont.integrableOn_Icc.mono_set (shortExceptional_subset (B r) W (V r)))
          ((hcontP.const_mul _).integrableOn_Icc.mono_set (shortExceptional_subset (B r) W (V r)))
          hmeas hpt
    _ = (V r ^ (2 * ℓ r))⁻¹
          * ∫ w in shortExceptional (B r) W (V r), ‖primeBlockPoly (B r) w ^ ℓ r * g w‖ ^ (2 : ℕ) :=
        integral_const_mul _ _
    _ ≤ (V r ^ (2 * ℓ r))⁻¹
          * ∫ w in Set.Icc (-W) W, ‖primeBlockPoly (B r) w ^ ℓ r * g w‖ ^ (2 : ℕ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_mono_set hcontP.integrableOn_Icc
          (Filter.Eventually.of_forall fun w => by positivity)
          (Filter.Eventually.of_forall (shortExceptional_subset (B r) W (V r)))

/-- **One first-small set.**  The blocks of the `j`-th range are small by membership; the cofactor
mean squares over the set are supplied. -/
theorem setIntegral_firstSmall_normSq_logPoly_moebius_le (P : ℕ → Finset ℕ) (R η : ℕ → ℝ)
    (L : ℕ → ℕ) (V : ℕ → ℕ → ℝ) (M : ℕ) {W δ : ℝ} (hδ : 0 < δ) (j : ℕ) (hR : 0 < R j)
    (hη : 0 ≤ η j) (hL : 1 ≤ L j) (hPprime : ∀ q ∈ P j, q.Prime)
    (hP : ∀ p ∈ P j, R j < (p : ℝ) ∧ (p : ℝ) ≤ R j * (1 + η j) ^ L j)
    (I : ℕ → ℝ)
    (hI : ∀ v ∈ Finset.range (L j), (∫ w in rangeFirstSmall P R η L V W j,
      ‖logPoly (ramareCofactorCoeff (P j)) (geomCofactorBlock M (R j) (η j) v) w‖ ^ (2 : ℕ))
        ≤ I v) :
    (∫ w in rangeFirstSmall P R η L V W j,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
      ≤ (1 + δ) * (2 * (L j : ℝ) * ∑ v ∈ Finset.range (L j), V j v ^ (2 : ℕ) * I v
            + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError (P j) M (R j) (η j) (L j) w‖ ^ 2)
        + (1 + 1 / δ)
            * (∫ w in Set.Icc (-W) W,
                ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet (P j) M) w‖ ^ 2) := by
  set E := rangeFirstSmall P R η L V W j with hE
  have hEm : MeasurableSet E := measurableSet_rangeFirstSmall P R η L V W j
  have hEs : E ⊆ Set.Icc (-W) W :=
    (rangeFirstSmall_subset P R η L V W j).trans (rangeAllSmall_subset P R η L V W j)
  have hbound : ∀ v ∈ Finset.range (L j), ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock (P j) (R j) (1 + η j) v) w‖ ≤ V j v := fun v hv w hw =>
    norm_primeBlockPoly_le_of_mem_allBlocksSmall hv (rangeFirstSmall_subset P R η L V W j hw)
  have hlad := setIntegral_normSq_ramareBilinear_le_ladder_supMeanSquare (P := P j) M hR hη hL
    hP hEm hEs (V j) I hbound hI
  have herr := setIntegral_normSq_ramareLadderError_le_window (P j) M (R j) (η j) (L j) hEs
  have hsplit := setIntegral_normSq_logPoly_moebius_le_ramare_rough (P := P j) hPprime M
    (W := W) hδ hEm hEs
  have hrough := setIntegral_normSq_logPoly_moebius_roughSet_le (P := P j) M (W := W) hEs
  have hδ0 : (0 : ℝ) ≤ 1 + δ := by linarith
  have hδ1 : (0 : ℝ) ≤ 1 + 1 / δ := by positivity
  have h1 := mul_le_mul_of_nonneg_left (hlad.trans (by linarith [herr] :
    2 * (L j : ℝ) * ∑ v ∈ Finset.range (L j), V j v ^ (2 : ℕ) * I v
      + 2 * ∫ w in E, ‖ramareLadderError (P j) M (R j) (η j) (L j) w‖ ^ (2 : ℕ)
      ≤ 2 * (L j : ℝ) * ∑ v ∈ Finset.range (L j), V j v ^ (2 : ℕ) * I v
        + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError (P j) M (R j) (η j) (L j) w‖ ^ 2)) hδ0
  have h2 := mul_le_mul_of_nonneg_left hrough hδ1
  linarith

/-- **The Möbius window over a ladder of prime ranges.**  Disc, first-small sets and the
exceptional half of the annulus, each with its own bound. -/
theorem integral_Icc_normSq_logPoly_moebius_le_multiRange (P : ℕ → Finset ℕ) (R η : ℕ → ℝ)
    (L : ℕ → ℕ) (V : ℕ → ℕ → ℝ) (M J : ℕ) {P' : Finset ℕ} {R' η' W w₀ δ Bdisc : ℝ}
    (hR : ∀ j ∈ Finset.range J, 0 < R j) (hη : ∀ j ∈ Finset.range J, 0 ≤ η j)
    (hL : ∀ j ∈ Finset.range J, 1 ≤ L j) (hPprime : ∀ j ∈ Finset.range J, ∀ q ∈ P j, q.Prime)
    (hP : ∀ j ∈ Finset.range J, ∀ p ∈ P j, R j < (p : ℝ) ∧ (p : ℝ) ≤ R j * (1 + η j) ^ L j)
    (I : ℕ → ℕ → ℝ)
    (hI : ∀ j ∈ Finset.range J, ∀ v ∈ Finset.range (L j), (∫ w in rangeFirstSmall P R η L V W j,
      ‖logPoly (ramareCofactorCoeff (P j)) (geomCofactorBlock M (R j) (η j) v) w‖ ^ (2 : ℕ))
        ≤ I j v)
    (hR' : 0 < R') (hη' : 0 ≤ η') (hW : 1 ≤ W) (hwW : w₀ ≤ W) {L' : ℕ} (hL' : 1 ≤ L')
    (hδ : 0 < δ) (hP'prime : ∀ q ∈ P', q.Prime)
    (hP' : ∀ p ∈ P', R' < (p : ℝ) ∧ (p : ℝ) ≤ R' * (1 + η') ^ L') (V' : ℕ → ℝ)
    (hNj : ∀ j ∈ Finset.range L', 1 ≤ ⌊(M : ℝ) / (R' * (1 + η') ^ j)⌋₊)
    (hbound' : ∀ j ∈ Finset.range L', ∀ w ∈ annulusLarge (rangeUnionSmall P R η L V W J) W w₀,
      ‖primeBlockPoly (geomBlock P' R' (1 + η') j) w‖ ≤ V' j)
    (hdisc : (∫ w in Set.Icc (-w₀) w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ Bdisc) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ Bdisc
        + ∑ j ∈ Finset.range J,
            ((1 + δ) * (2 * (L j : ℝ) * ∑ v ∈ Finset.range (L j), V j v ^ (2 : ℕ) * I j v
                + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError (P j) M (R j) (η j) (L j) w‖ ^ 2)
              + (1 + 1 / δ)
                * (∫ w in Set.Icc (-W) W,
                    ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet (P j) M) w‖ ^ 2))
        + ((1 + δ) * (2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
                V' j ^ 2 * ladderHMBoundRecip M R' η' W
                    (volume.real (annulusLarge (rangeUnionSmall P R η L V W J) W w₀)) j
              + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P' M R' η' L' w‖ ^ 2)
          + (1 + 1 / δ)
              * (∫ w in Set.Icc (-W) W,
                  ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P' M) w‖ ^ 2)) := by
  have hcont : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  refine integral_Icc_normSq_logPoly_moebius_le_partition M hwW
    (measurableSet_rangeUnionSmall P R η L V W J) (rangeUnionSmall_subset P R η L V W J) hdisc
    ?_ ?_
  · refine (setIntegral_annulusSmall_le_sum_firstSmall P R η L V W w₀ J hcont
      fun t => by positivity).trans (Finset.sum_le_sum fun j hj => ?_)
    exact setIntegral_firstSmall_normSq_logPoly_moebius_le P R η L V M hδ j (hR j hj) (hη j hj)
      (hL j hj) (hPprime j hj) (hP j hj) (I j) (hI j hj)
  · exact setIntegral_annulusLarge_normSq_logPoly_moebius_le M hR' hη' hW hL' hδ hP'prime hP'
      (measurableSet_rangeUnionSmall P R η L V W J) V' hNj hbound'

/-- The exceptional half of the annulus lies in the exceptional set of any single range. -/
theorem annulusLarge_rangeUnionSmall_subset (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (W w₀ : ℝ) {J j : ℕ} (hj : j < J) :
    annulusLarge (rangeUnionSmall P R η L V W J) W w₀
      ⊆ annulusLarge (rangeAllSmall P R η L V W j) W w₀ := by
  intro w hw
  refine ⟨⟨hw.1.1, fun h => hw.1.2 ?_⟩, hw.2⟩
  exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, h⟩

end

end RHTower.Sieve
