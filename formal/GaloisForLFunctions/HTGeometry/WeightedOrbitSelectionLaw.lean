import GaloisForLFunctions.HTGeometry.WeightedOrbitInductionSchatten
import GaloisForLFunctions.HTGeometry.WeightedOrbitPacketInformation
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Weighted orbit induction: selection phase diagram, neutrality, no-gos, and recovery

This module assembles the weighted orbit-induction laws into the global selection statements.

* **Phase diagram.**  `phaseDiagram_essential`, `phaseDiagram_compact_not_schatten`,
  `phaseDiagram_schatten`, `phaseDiagram_gap` give the four regimes: amplitudes outside `c₀`
  (essential operator), in `c₀ \ ℓ^p` (compact, not Schatten), in `ℓ^p` (Schatten), and with a
  positive reduced gap (closed range, Fredholm exactly for an invertible block); the information
  column is the summability of the local divergences.  `amplitude_regimes` exhibits amplitude
  families realizing every combination of ideal class and reduced gap.
* **Functional-equation neutrality.**  Every regime-defining quantity — `‖a‖_∞`, `α_*(a)`, the
  tail supremum, `c₀`, `ℓ^p`, the operator norm, essential norm, Schatten energy, reduced gap, and
  the total information — is invariant under any reindexing of the orbit and any measurable
  exchange of the packets.
* **Sharp no-gos** 9.1–9.6.
* **Source gate** `(WOI.14)`: the four global invariants are the four amplitude/information
  quantities times local constants.
* **Recovery--regularization uncertainty** `(WOI.15)`–`(WOI.18)`: a bounded left inverse `L` of a
  formation `T` forces `‖T x‖ ≥ ‖x‖ / ‖L‖`, the diagonal formation has a bounded left inverse
  exactly when `inf |aᵢ| > 0`, and a compact or Schatten formation of an infinite orbit has no
  bounded coefficient-faithful decoder.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter RHTower MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Topology InnerProductSpace

noncomputable section

/-! ## Amplitude quantities -/

section Amplitudes

variable {I : Type} [Nonempty I] [DecidableEq I]

omit [Nonempty I] [DecidableEq I] in
/-- If infinitely many amplitudes are nonzero and the amplitudes tend to zero, the reduced gap
vanishes. -/
theorem ampGap_eq_zero_of_tendsto {a : I → ℂ} (hinf : {i | a i ≠ 0}.Infinite)
    (hlim : Tendsto a cofinite (𝓝 0)) : ampGap a = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (ampGap_nonneg a)
  rw [zero_add]
  have hfin : {i | ε ≤ ‖a i‖}.Finite := by
    rw [Metric.tendsto_nhds] at hlim
    have := hlim ε hε
    rw [Filter.eventually_cofinite] at this
    simpa [dist_zero_right, not_lt] using this
  obtain ⟨i, hi, hni⟩ := (hinf.sdiff hfin).nonempty
  have hlt : ‖a i‖ < ε := by simpa using hni
  exact (ampGap_le hi).trans hlt.le

omit [Nonempty I] in
/-- The tail supremum is invariant under reindexing of the orbit. -/
theorem tailSup_comp_perm (σ : Equiv.Perm I) (a : I → ℂ) : tailSup (a ∘ σ) = tailSup a := by
  have hstep : ∀ F : Finset I,
      ampSup (tailAmp F (a ∘ σ)) = ampSup (tailAmp (σ.finsetCongr F) a) := by
    intro F
    have hpt : ∀ i, ‖tailAmp F (a ∘ σ) i‖ = ‖tailAmp (σ.finsetCongr F) a (σ i)‖ := by
      intro i
      simp only [tailAmp, Function.comp_apply, Equiv.finsetCongr_apply, Finset.mem_map_equiv,
        Equiv.symm_apply_apply]
    rw [ampSup, ampSup]
    simp_rw [hpt]
    exact Equiv.iSup_comp (g := fun j => ‖tailAmp (σ.finsetCongr F) a j‖) σ
  rw [tailSup, tailSup]
  simp_rw [hstep]
  exact Equiv.iInf_comp (g := fun G => ampSup (tailAmp G a)) σ.finsetCongr

omit [Nonempty I] [DecidableEq I] in
theorem ampSup_comp_perm (σ : Equiv.Perm I) (a : I → ℂ) : ampSup (a ∘ σ) = ampSup a :=
  Equiv.iSup_comp (g := fun j => ‖a j‖) σ

omit [Nonempty I] [DecidableEq I] in
theorem ampGap_comp_perm (σ : Equiv.Perm I) (a : I → ℂ) : ampGap (a ∘ σ) = ampGap a :=
  Equiv.iInf_comp (g := fun j : {i : I // a i ≠ 0} => ‖a j‖)
    (σ.subtypeEquiv fun _ => Iff.rfl)

omit [Nonempty I] [DecidableEq I] in
theorem bddAbove_comp_perm (σ : Equiv.Perm I) {a : I → ℂ}
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    BddAbove (Set.range fun i => ‖(a ∘ σ) i‖) := by
  obtain ⟨M, hM⟩ := hbdd
  exact ⟨M, by rintro _ ⟨i, rfl⟩; exact hM ⟨σ i, rfl⟩⟩

end Amplitudes

/-! ## Section 7: the global selection phase diagram -/

section PhaseDiagram

variable {I : Type} [Nonempty I] [DecidableEq I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {Z Wz : I → Type*} [∀ i, MeasurableSpace (Z i)] [∀ i, MeasurableSpace (Wz i)]

/-- The recovered packet work along an exhaustion. -/
def exhaustionWork (Fn : ℕ → Finset I) (P Q : ∀ i, Measure (Z i))
    (κ : ∀ i, ProbabilityTheory.Kernel (Z i) (Wz i)) (n : ℕ) : ℝ≥0∞ :=
  formationJeffreys (independentPacket (Fn n) fun i => splitPacketLaw (P i) (κ i))
    (independentPacket (Fn n) fun i => splitPacketLaw (Q i) (κ i))

/-- **Section 7, first row.**  Amplitudes outside `c₀` and nonsummable local information: the
global operator is essential (noncompact, with positive essential norm) and the global
information is infinite. -/
theorem phaseDiagram_essential (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hD : IsCompactOperator D) (hDne : D ≠ 0) {Fn : ℕ → Finset I} (hmono : Monotone Fn)
    (hexh : ∀ i, ∃ n, i ∈ Fn n) (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] (κ : ∀ i, ProbabilityTheory.Kernel (Z i) (Wz i))
    [∀ i, IsMarkovKernel (κ i)] (ha : ¬ Tendsto a cofinite (𝓝 0))
    (hj : ∑' i, formationJeffreys (P i) (Q i) = ⊤) :
    ¬ IsCompactOperator (weightedInduction a D U V hbdd)
      ∧ 0 < rectEssentialNorm (weightedInduction a D U V hbdd)
      ∧ ⨆ n, exhaustionWork Fn P Q κ n = ⊤ := by
  have htail : tailSup a ≠ 0 := fun h => ha ((tailSup_eq_zero_iff_tendsto hbdd).mp h)
  refine ⟨fun hc => ha ((isCompactOperator_weightedInduction_iff_tendsto a D U V hbdd hD
    hDne).mp hc), ?_, ?_⟩
  · rw [rectEssentialNorm_weightedInduction a D U V hbdd hD]
    exact mul_pos (lt_of_le_of_ne (tailSup_nonneg hbdd) (Ne.symm htail))
      (norm_pos_iff.mpr hDne)
  · unfold exhaustionWork
    rw [iSup_formationJeffreys_exhaustion hmono hexh P Q κ, hj]

/-- **Section 7, second row.**  Amplitudes in `c₀ \ ℓ^p` and nonsummable local information: the
ideal is repaired (compact) but the Schatten class is not reached, and the work still selects. -/
theorem phaseDiagram_compact_not_schatten [Countable I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    {p : ℝ} (hp : 0 < p) (hDS : MemRectSchattenClass p D) (hDne : D ≠ 0)
    {Fn : ℕ → Finset I} (hmono : Monotone Fn)
    (hexh : ∀ i, ∃ n, i ∈ Fn n) (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] (κ : ∀ i, ProbabilityTheory.Kernel (Z i) (Wz i))
    [∀ i, IsMarkovKernel (κ i)] (ha : Tendsto a cofinite (𝓝 0))
    (hap : ¬ Summable fun i => ‖a i‖ ^ p) (hj : ∑' i, formationJeffreys (P i) (Q i) = ⊤) :
    IsCompactOperator (weightedInduction a D U V hbdd)
      ∧ ¬ MemRectSchattenClass p (weightedInduction a D U V hbdd)
      ∧ ⨆ n, exhaustionWork Fn P Q κ n = ⊤ := by
  have hD := isCompactOperator_of_memRectSchattenClass hp hDS
  refine ⟨(isCompactOperator_weightedInduction_iff_tendsto a D U V hbdd hD hDne).mpr ha,
    fun h => hap ((memRectSchattenClass_weightedInduction_iff a D U V hbdd hp hDS hDne).mp h),
    ?_⟩
  unfold exhaustionWork
  rw [iSup_formationJeffreys_exhaustion hmono hexh P Q κ, hj]

/-- **Section 7, third row.**  Amplitudes in `ℓ^p` and summable local information: the global
operator is Schatten and the global information is finite, so a nonzero local defect can remain
admitted. -/
theorem phaseDiagram_schatten [Countable I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    {p : ℝ} (hp : 0 < p) (hDS : MemRectSchattenClass p D) (hDne : D ≠ 0)
    {Fn : ℕ → Finset I} (hmono : Monotone Fn)
    (hexh : ∀ i, ∃ n, i ∈ Fn n) (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] (κ : ∀ i, ProbabilityTheory.Kernel (Z i) (Wz i))
    [∀ i, IsMarkovKernel (κ i)] (hap : Summable fun i => ‖a i‖ ^ p)
    (hj : ∑' i, formationJeffreys (P i) (Q i) ≠ ⊤) :
    MemRectSchattenClass p (weightedInduction a D U V hbdd)
      ∧ ⨆ n, exhaustionWork Fn P Q κ n < ⊤ := by
  refine ⟨(memRectSchattenClass_weightedInduction_iff a D U V hbdd hp hDS hDne).mpr hap, ?_⟩
  unfold exhaustionWork
  rw [iSup_formationJeffreys_exhaustion hmono hexh P Q κ]
  exact lt_top_iff_ne_top.mpr hj

/-- **Section 7, fourth row.**  With a positive reduced gap the range is closed exactly when the
local range is; over an infinite orbit with all amplitudes nonzero the induction is Fredholm
exactly when the local block is invertible. -/
theorem phaseDiagram_gap (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hne : ∃ i, a i ≠ 0)
    (hDne : D ≠ 0) (hgap : 0 < ampGap a) :
    (IsClosed (Set.range (weightedInduction a D U V hbdd)) ↔ IsClosed (Set.range D))
      ∧ ([Infinite I] → (∀ i, a i ≠ 0) →
        (IsBoundedFredholm (weightedInduction a D U V hbdd) ↔ Function.Bijective D)) := by
  refine ⟨?_, fun ha => ?_⟩
  · rw [isClosed_range_weightedInduction_iff_ampGap a D U V hbdd hne hDne]
    exact ⟨fun h => h.1, fun h => ⟨h, hgap⟩⟩
  · rw [isBoundedFredholm_weightedInduction_iff a D U V hbdd ha hDne]
    exact ⟨fun h => h.1, fun h => ⟨h, hgap⟩⟩

end PhaseDiagram

/-! ## Amplitude families realizing every regime -/

section Regimes

/-- The amplitude family `aₙ = (n+1)^{-s}`. -/
def powerAmp (s : ℝ) (n : ℕ) : ℂ := (((n + 1 : ℝ) ^ (-s) : ℝ) : ℂ)

theorem norm_powerAmp (s : ℝ) (n : ℕ) : ‖powerAmp s n‖ = (n + 1 : ℝ) ^ (-s) := by
  rw [powerAmp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem powerAmp_ne_zero (s : ℝ) (n : ℕ) : powerAmp s n ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_powerAmp]
  positivity

theorem norm_powerAmp_le_one {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : ‖powerAmp s n‖ ≤ 1 := by
  rw [norm_powerAmp]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    (by linarith)

theorem bddAbove_powerAmp {s : ℝ} (hs : 0 ≤ s) :
    BddAbove (Set.range fun n => ‖powerAmp s n‖) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact norm_powerAmp_le_one hs n

theorem tendsto_powerAmp {s : ℝ} (hs : 0 < s) : Tendsto (powerAmp s) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_powerAmp]
  have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop hs).comp h1

theorem summable_norm_powerAmp_rpow_iff {s p : ℝ} :
    (Summable fun n => ‖powerAmp s n‖ ^ p) ↔ 1 < s * p := by
  have heq : ∀ n : ℕ, ‖powerAmp s n‖ ^ p = 1 / ((n + 1 : ℕ) : ℝ) ^ (s * p) := by
    intro n
    rw [norm_powerAmp, ← Real.rpow_mul (by positivity), one_div, ← Real.rpow_neg (by positivity)]
    push_cast
    ring_nf
  simp_rw [heq]
  rw [summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (s * p)) 1,
    Real.summable_one_div_nat_rpow]

/-- **Section 7: the regimes are all realized, and ideal class and reduced gap are independent.**
On `ℕ`, for every exponent `p > 0`:
* constant amplitudes are outside `c₀` with gap `1`;
* `(n+1)^{-1/p}` is in `c₀ \ ℓ^p` with gap `0`;
* `(n+1)^{-2/p}` is in `ℓ^p` with gap `0`;
* the amplitude supported at one index is in `ℓ^p` with gap `1`;
* amplitudes alternating between `1` and `(n+1)^{-1}` are outside `c₀` with gap `0`. -/
theorem amplitude_regimes {p : ℝ} (hp : 0 < p) :
    (tailSup (fun _ : ℕ => (1 : ℂ)) ≠ 0 ∧ ampGap (fun _ : ℕ => (1 : ℂ)) = 1)
    ∧ (tailSup (powerAmp (1 / p)) = 0 ∧ ¬ Summable (fun n => ‖powerAmp (1 / p) n‖ ^ p)
        ∧ ampGap (powerAmp (1 / p)) = 0)
    ∧ (Summable (fun n => ‖powerAmp (2 / p) n‖ ^ p) ∧ ampGap (powerAmp (2 / p)) = 0)
    ∧ (Summable (fun n => ‖(fun m : ℕ => if m = 0 then (1 : ℂ) else 0) n‖ ^ p)
        ∧ ampGap (fun m : ℕ => if m = 0 then (1 : ℂ) else 0) = 1)
    ∧ (tailSup (fun m : ℕ => if Even m then (1 : ℂ) else powerAmp 1 m) ≠ 0
        ∧ ampGap (fun m : ℕ => if Even m then (1 : ℂ) else powerAmp 1 m) = 0) := by
  have hone : BddAbove (Set.range fun _ : ℕ => ‖(1 : ℂ)‖) := ⟨1, by rintro _ ⟨_, rfl⟩; simp⟩
  have hinfNat : ∀ {s : Set ℕ}, s = Set.univ → s.Infinite := fun h => h ▸ Set.infinite_univ
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have := ((tailSup_eq_zero_iff hone).mp h) 1 one_pos
    exact hinfNat (by ext; simp) this
  · refine le_antisymm (ampGap_le (i := 0) one_ne_zero |>.trans (by simp)) ?_
    exact le_ampGap ⟨0, one_ne_zero⟩ fun _ _ => by simp
  · exact (tailSup_eq_zero_iff_tendsto (bddAbove_powerAmp (by positivity))).mpr
      (tendsto_powerAmp (by positivity))
  · rw [summable_norm_powerAmp_rpow_iff, one_div_mul_cancel hp.ne']
    exact lt_irrefl 1
  · exact ampGap_eq_zero_of_tendsto (hinfNat (by ext n; simp [powerAmp_ne_zero]))
      (tendsto_powerAmp (by positivity))
  · rw [summable_norm_powerAmp_rpow_iff, div_mul_cancel₀ 2 hp.ne']
    norm_num
  · exact ampGap_eq_zero_of_tendsto (hinfNat (by ext n; simp [powerAmp_ne_zero]))
      (tendsto_powerAmp (by positivity))
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0, Real.zero_rpow hp.ne']
  · refine le_antisymm ((ampGap_le (i := 0) (by simp)).trans (by simp)) ?_
    refine le_ampGap ⟨0, by simp⟩ fun i hi => ?_
    by_cases h0 : i = 0
    · simp [h0]
    · simp [h0] at hi
  · intro h
    have hbdd : BddAbove (Set.range fun m : ℕ =>
        ‖(fun m : ℕ => if Even m then (1 : ℂ) else powerAmp 1 m) m‖) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨m, rfl⟩
      by_cases hm : Even m
      · simp [hm]
      · simp only [hm, if_false]
        exact norm_powerAmp_le_one zero_le_one m
    have hfin := ((tailSup_eq_zero_iff hbdd).mp h) 1 one_pos
    have hsub : {m : ℕ | Even m} ⊆ {m : ℕ | 1 ≤ ‖(fun m : ℕ =>
        if Even m then (1 : ℂ) else powerAmp 1 m) m‖} := by
      intro m hm
      simp only [Set.mem_setOf_eq] at hm ⊢
      simp [hm]
    exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
      (fun x y hxy => by simp only at hxy; omega) (fun n => even_two_mul n) (hfin.subset hsub)
  · refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (ampGap_nonneg _)
    rw [zero_add]
    have hev : ∀ᶠ n : ℕ in atTop, ‖powerAmp 1 n‖ < ε := by
      have := (tendsto_zero_iff_norm_tendsto_zero.mp
        (Nat.cofinite_eq_atTop ▸ tendsto_powerAmp one_pos))
      exact this.eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have hodd : ¬ Even (2 * N + 1) := by
      rw [Nat.not_even_iff_odd]
      exact odd_two_mul_add_one N
    have hne : (fun m : ℕ => if Even m then (1 : ℂ) else powerAmp 1 m) (2 * N + 1) ≠ 0 := by
      simp only [hodd, if_false]
      exact powerAmp_ne_zero 1 _
    refine (ampGap_le (a := fun m : ℕ => if Even m then (1 : ℂ) else powerAmp 1 m)
      (i := 2 * N + 1) hne).trans ?_
    simp only [hodd, if_false]
    exact (hN (2 * N + 1) (by omega)).le

end Regimes

/-! ## Section 8: functional-equation neutrality -/

section Neutrality

variable {I : Type} [Nonempty I] [DecidableEq I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Section 8 (1).**  A reindexing of the orbit preserves `‖a‖_∞`, `α_*(a)`, the tail supremum,
the `c₀` condition, every `ℓ^p` condition and every `ℓ^p` sum. -/
theorem amplitude_neutrality (σ : Equiv.Perm I) (a : I → ℂ)
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (p : ℝ) :
    ampSup (a ∘ σ) = ampSup a ∧ ampGap (a ∘ σ) = ampGap a ∧ tailSup (a ∘ σ) = tailSup a
      ∧ (Tendsto (a ∘ σ) cofinite (𝓝 0) ↔ Tendsto a cofinite (𝓝 0))
      ∧ ((Summable fun i => ‖(a ∘ σ) i‖ ^ p) ↔ Summable fun i => ‖a i‖ ^ p)
      ∧ ∑' i, ‖(a ∘ σ) i‖ ^ p = ∑' i, ‖a i‖ ^ p := by
  refine ⟨ampSup_comp_perm σ a, ampGap_comp_perm σ a, tailSup_comp_perm σ a, ?_, ?_, ?_⟩
  · rw [← tailSup_eq_zero_iff_tendsto (bddAbove_comp_perm σ hbdd),
      ← tailSup_eq_zero_iff_tendsto hbdd, tailSup_comp_perm]
  · exact σ.summable_iff (f := fun i => ‖a i‖ ^ p)
  · exact σ.tsum_eq (fun i => ‖a i‖ ^ p)

/-- **Section 8 (2).**  A reindexing of the orbit, combined with any new unitary transports (in
particular the dual ones), preserves the operator norm, the essential norm, the Schatten energy,
and the reduced gap of the weighted induction. -/
theorem operator_neutrality [Countable I] (σ : Equiv.Perm I) (a : I → ℂ) (D : H →L[ℂ] K)
    (U U' : I → (H ≃ₗᵢ[ℂ] H)) (V V' : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    ‖weightedInduction (a ∘ σ) D U' V' (bddAbove_comp_perm σ hbdd)‖
        = ‖weightedInduction a D U V hbdd‖
      ∧ (IsCompactOperator D →
          rectEssentialNorm (weightedInduction (a ∘ σ) D U' V' (bddAbove_comp_perm σ hbdd))
            = rectEssentialNorm (weightedInduction a D U V hbdd))
      ∧ (IsCompactOperator D → ∀ {p : ℝ}, 0 < p →
          ∑' n, ENNReal.ofReal (rectApproxNumber
              (weightedInduction (a ∘ σ) D U' V' (bddAbove_comp_perm σ hbdd)) n ^ p)
            = ∑' n, ENNReal.ofReal (rectApproxNumber (weightedInduction a D U V hbdd) n ^ p))
      ∧ ((∃ i, a i ≠ 0) → D ≠ 0 →
          reducedMinModulus (weightedInduction (a ∘ σ) D U' V' (bddAbove_comp_perm σ hbdd))
            = reducedMinModulus (weightedInduction a D U V hbdd)) := by
  refine ⟨?_, fun hD => ?_, fun hD p hp => ?_, fun hne hD => ?_⟩
  · rw [norm_weightedInduction, norm_weightedInduction, ampSup_comp_perm]
  · rw [rectEssentialNorm_weightedInduction _ _ _ _ _ hD,
      rectEssentialNorm_weightedInduction _ _ _ _ _ hD, tailSup_comp_perm]
  · rw [tsum_ofReal_rpow_rectApproxNumber_weightedInduction _ _ _ _ _ hD hp,
      tsum_ofReal_rpow_rectApproxNumber_weightedInduction _ _ _ _ _ hD hp]
    congr 1
    exact σ.tsum_eq (fun i => ENNReal.ofReal (‖a i‖ ^ p))
  · obtain ⟨i, hi⟩ := hne
    have hne' : ∃ j, (a ∘ σ) j ≠ 0 := ⟨σ.symm i, by simpa using hi⟩
    rw [reducedMinModulus_weightedInduction _ _ _ _ _ hne' hD,
      reducedMinModulus_weightedInduction _ _ _ _ _ ⟨i, hi⟩ hD, ampGap_comp_perm]

omit [Nonempty I] [DecidableEq I] in
/-- **Section 8 (3).**  Exchanging the packets by measurable bijections and reindexing the orbit
preserves every local information `jᵢ` and the total information. -/
theorem information_neutrality {Z Z' : I → Type*} [∀ i, MeasurableSpace (Z i)]
    [∀ i, MeasurableSpace (Z' i)] (σ : Equiv.Perm I) (e : ∀ i, Z (σ i) ≃ᵐ Z' i)
    (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    (∀ i, formationJeffreys ((P (σ i)).map (e i)) ((Q (σ i)).map (e i))
        = formationJeffreys (P (σ i)) (Q (σ i)))
      ∧ ∑' i, formationJeffreys ((P (σ i)).map (e i)) ((Q (σ i)).map (e i))
        = ∑' i, formationJeffreys (P i) (Q i) := by
  have hloc : ∀ i, formationJeffreys ((P (σ i)).map (e i)) ((Q (σ i)).map (e i))
      = formationJeffreys (P (σ i)) (Q (σ i)) := by
    intro i
    rw [formationJeffreys, formationJeffreys,
      klDiv_map_measurableEmbedding (e i).measurableEmbedding,
      klDiv_map_measurableEmbedding (e i).measurableEmbedding]
  refine ⟨hloc, ?_⟩
  simp_rw [hloc]
  exact σ.tsum_eq (fun i => formationJeffreys (P i) (Q i))

end Neutrality

/-! ## Section 9: sharp no-gos -/

section NoGo

variable {I : Type} [Nonempty I] [DecidableEq I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **No-go 9.1.**  An infinite orbit does not force neutrality: a nonzero compact block with
`c₀` amplitudes has compact global induction. -/
theorem noGo_infiniteOrbit_compact (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hD : IsCompactOperator D) (ha : Tendsto a cofinite (𝓝 0)) :
    IsCompactOperator (weightedInduction a D U V hbdd) := by
  refine isCompactOperator_of_rectEssentialNorm_eq_zero ?_
  rw [rectEssentialNorm_weightedInduction a D U V hbdd hD,
    (tailSup_eq_zero_iff_tendsto hbdd).mpr ha, zero_mul]

/-- **No-go 9.1, witness.**  On `ℓ²(ℕ)` the identity of `ℂ`, a nonzero compact block, weighted
by `(n+1)^{-1}`, has compact global induction over an infinite orbit. -/
theorem exists_compact_weightedInduction_nonzero_block :
    ∃ (a : ℕ → ℂ) (hbdd : BddAbove (Set.range fun i => ‖a i‖)),
      IsCompactOperator (weightedInduction a (ContinuousLinearMap.id ℂ ℂ)
        (fun _ => LinearIsometryEquiv.refl ℂ ℂ) (fun _ => LinearIsometryEquiv.refl ℂ ℂ) hbdd)
      ∧ ContinuousLinearMap.id ℂ ℂ ≠ 0 := by
  refine ⟨powerAmp 1, bddAbove_powerAmp zero_le_one, ?_, ?_⟩
  · exact noGo_infiniteOrbit_compact _ _ _ _ _
      (isCompactOperator_of_locallyCompactSpace_dom _) (tendsto_powerAmp one_pos)
  · intro h
    have := congrArg (fun T : ℂ →L[ℂ] ℂ => T 1) h
    simp at this

/-- **No-go 9.2.**  Compactness of the global defect forces `|aᵢ| ‖D‖ → 0`, for every bounded
block `D`; it does not force `D = 0` (see `exists_compact_weightedInduction_nonzero_block`). -/
theorem noGo_compact_forces_decay (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hc : IsCompactOperator (weightedInduction a D U V hbdd)) :
    Tendsto (fun i => ‖a i‖ * ‖D‖) cofinite (𝓝 0) := by
  have hle := le_rectEssentialNorm_weightedInduction a D U V hbdd
  rw [rectEssentialNorm_eq_zero_of_isCompactOperator hc] at hle
  rcases eq_or_lt_of_le (norm_nonneg D) with h0 | hpos
  · simpa [← h0] using tendsto_const_nhds
  · have htail : tailSup a = 0 := le_antisymm
      (by nlinarith [tailSup_nonneg hbdd]) (tailSup_nonneg hbdd)
    have ht := (tailSup_eq_zero_iff_tendsto hbdd).mp htail
    simpa using (tendsto_zero_iff_norm_tendsto_zero.mp ht).mul_const ‖D‖

omit [DecidableEq I] in
/-- **No-go 9.3.**  Trace-class local blocks do not give trace-class formation: the homogeneous
orbit of a nonzero trace-class block over an infinite countable orbit is not trace class. -/
theorem noGo_traceClass_homogeneous [Countable I] [Infinite I] (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (h1 : BddAbove (Set.range fun i => ‖(fun _ : I => (1 : ℂ)) i‖))
    (hDS : MemRectSchattenClass 1 D) (hD0 : D ≠ 0) :
    ¬ MemRectSchattenClass 1 (weightedInduction (fun _ => 1) D U V h1) := by
  rw [memRectSchattenClass_one_weightedInduction_iff _ D U V h1 hDS hD0]
  intro hs
  have ht := hs.tendsto_cofinite_zero
  simp only [norm_one] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

omit [DecidableEq I] in
/-- **No-go 9.4.**  Amplitude decay does not give closed range: if infinitely many amplitudes are
nonzero and they tend to zero, the reduced minimum modulus vanishes and the range is not closed
for every nonzero block. -/
theorem noGo_decay_not_closed (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hinf : {i | a i ≠ 0}.Infinite) (hlim : Tendsto a cofinite (𝓝 0)) (hD : D ≠ 0) :
    reducedMinModulus (weightedInduction a D U V hbdd) = 0
      ∧ ¬ IsClosed (Set.range (weightedInduction a D U V hbdd)) := by
  have hne : ∃ i, a i ≠ 0 := hinf.nonempty
  have hgap := ampGap_eq_zero_of_tendsto hinf hlim
  refine ⟨by rw [reducedMinModulus_weightedInduction a D U V hbdd hne hD, hgap, zero_mul], ?_⟩
  rw [isClosed_range_weightedInduction_iff_ampGap a D U V hbdd hne hD, hgap]
  exact fun h => lt_irrefl 0 h.2

end NoGo

/-! ## Section 10: the source gate -/

section Gate

variable {I : Type} [Nonempty I] [DecidableEq I] [Countable I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {Z Wz : I → Type*} [∀ i, MeasurableSpace (Z i)] [∀ i, MeasurableSpace (Wz i)]

/-- **`(WOI.14)`, the source gate.**  The four global invariants of a weighted orbit — essential
norm, reduced minimum modulus, Schatten `p`-energy, and total recovered information — are exactly
the four quantities `limsup |aᵢ|`, `inf_{aᵢ≠0} |aᵢ|`, `∑ |aᵢ|^p`, `∑ J(Pᵢ,Qᵢ)` times local
constants. -/
theorem weightedOrbit_sourceGate (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hD : IsCompactOperator D) (hDne : D ≠ 0) (hne : ∃ i, a i ≠ 0) {p : ℝ} (hp : 0 < p)
    {Fn : ℕ → Finset I} (hmono : Monotone Fn) (hexh : ∀ i, ∃ n, i ∈ Fn n)
    (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] (κ : ∀ i, ProbabilityTheory.Kernel (Z i) (Wz i))
    [∀ i, IsMarkovKernel (κ i)] :
    rectEssentialNorm (weightedInduction a D U V hbdd) = tailSup a * ‖D‖
      ∧ reducedMinModulus (weightedInduction a D U V hbdd) = ampGap a * reducedMinModulus D
      ∧ ∑' n, ENNReal.ofReal (rectApproxNumber (weightedInduction a D U V hbdd) n ^ p)
          = (∑' i, ENNReal.ofReal (‖a i‖ ^ p))
              * ∑' n, ENNReal.ofReal (rectApproxNumber D n ^ p)
      ∧ ⨆ n, exhaustionWork Fn P Q κ n = ∑' i, formationJeffreys (P i) (Q i) :=
  ⟨rectEssentialNorm_weightedInduction a D U V hbdd hD,
    reducedMinModulus_weightedInduction a D U V hbdd hne hDne,
    tsum_ofReal_rpow_rectApproxNumber_weightedInduction a D U V hbdd hD hp,
    iSup_formationJeffreys_exhaustion hmono hexh P Q κ⟩

end Gate

/-! ## Section 11: uniform recovery--regularization uncertainty -/

section Recovery

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **Theorem 11.1, `(WOI.16)`, product form.**  A bounded left inverse `L` of a formation `T`
gives `‖x‖ ≤ ‖L‖ ‖T x‖`. -/
theorem norm_le_norm_leftInverse_mul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {T : X →L[𝕜] Y} {L : Y →L[𝕜] X}
    (hLT : L.comp T = ContinuousLinearMap.id 𝕜 X) (x : X) : ‖x‖ ≤ ‖L‖ * ‖T x‖ := by
  have h : L (T x) = x := by
    rw [← ContinuousLinearMap.comp_apply, hLT, ContinuousLinearMap.id_apply]
  calc ‖x‖ = ‖L (T x)‖ := by rw [h]
    _ ≤ ‖L‖ * ‖T x‖ := L.le_opNorm _

/-- **Theorem 11.1, `(WOI.16)`.**  `‖T x‖ ≥ ‖x‖ / ‖L‖`. -/
theorem div_norm_leftInverse_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {T : X →L[𝕜] Y} {L : Y →L[𝕜] X}
    (hLT : L.comp T = ContinuousLinearMap.id 𝕜 X) (x : X) : ‖x‖ / ‖L‖ ≤ ‖T x‖ := by
  rcases eq_or_lt_of_le (norm_nonneg L) with h0 | hpos
  · rw [← h0, div_zero]
    exact norm_nonneg _
  · rw [div_le_iff₀ hpos, mul_comm]
    exact norm_le_norm_leftInverse_mul hLT x

variable {X Y : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace 𝕜 (X n)]
  [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace 𝕜 (Y n)]

/-- **Theorem 11.1 (1).**  Uniformly bounded recovery transmits divergence of the source to the
formation. -/
theorem tendsto_norm_formation_of_bounded_recovery {T : ∀ n, X n →L[𝕜] Y n}
    {L : ∀ n, Y n →L[𝕜] X n} (hLT : ∀ n, (L n).comp (T n) = ContinuousLinearMap.id 𝕜 (X n))
    {x : ∀ n, X n} (hL : ∃ C, ∀ n, ‖L n‖ ≤ C) (hx : Tendsto (fun n => ‖x n‖) atTop atTop) :
    Tendsto (fun n => ‖T n (x n)‖) atTop atTop := by
  obtain ⟨C, hC⟩ := hL
  have hC' : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine tendsto_atTop_mono (fun n => ?_) (hx.atTop_div_const hC')
  rw [div_le_iff₀ hC']
  calc ‖x n‖ ≤ ‖L n‖ * ‖T n (x n)‖ := norm_le_norm_leftInverse_mul (hLT n) (x n)
    _ ≤ max C 1 * ‖T n (x n)‖ :=
      mul_le_mul_of_nonneg_right ((hC n).trans (le_max_left _ _)) (norm_nonneg _)
    _ = ‖T n (x n)‖ * max C 1 := mul_comm _ _

/-- **Theorem 11.1 (2).**  A divergent source with bounded formation forces the recovery norms to
diverge. -/
theorem tendsto_norm_recovery_of_bounded_formation {T : ∀ n, X n →L[𝕜] Y n}
    {L : ∀ n, Y n →L[𝕜] X n} (hLT : ∀ n, (L n).comp (T n) = ContinuousLinearMap.id 𝕜 (X n))
    {x : ∀ n, X n} (hx : Tendsto (fun n => ‖x n‖) atTop atTop)
    (hT : ∃ M, ∀ n, ‖T n (x n)‖ ≤ M) :
    Tendsto (fun n => ‖L n‖) atTop atTop := by
  obtain ⟨M, hM⟩ := hT
  have hM' : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine tendsto_atTop_mono (fun n => ?_) (hx.atTop_div_const hM')
  rw [div_le_iff₀ hM']
  calc ‖x n‖ ≤ ‖L n‖ * ‖T n (x n)‖ := norm_le_norm_leftInverse_mul (hLT n) (x n)
    _ ≤ ‖L n‖ * max M 1 :=
      mul_le_mul_of_nonneg_left ((hM n).trans (le_max_left _ _)) (norm_nonneg _)

/-- **Theorem 11.1 (3).**  No uniformly recoverable formation regularizes a divergent source
history into one bounded target history. -/
theorem not_bounded_recovery_and_regularization {T : ∀ n, X n →L[𝕜] Y n}
    {L : ∀ n, Y n →L[𝕜] X n} (hLT : ∀ n, (L n).comp (T n) = ContinuousLinearMap.id 𝕜 (X n))
    {x : ∀ n, X n} :
    ¬ ((∃ C, ∀ n, ‖L n‖ ≤ C) ∧ Tendsto (fun n => ‖x n‖) atTop atTop
        ∧ ∃ M, ∀ n, ‖T n (x n)‖ ≤ M) := by
  rintro ⟨hL, hx, M, hM⟩
  obtain ⟨n, hn⟩ :=
    ((tendsto_norm_formation_of_bounded_recovery hLT hL hx).eventually_gt_atTop M).exists
  exact absurd (hM n) (not_le.mpr hn)

end Recovery

section Diagonal

variable {I : Type} [Nonempty I] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal formation `A_a (xᵢ) = (aᵢ xᵢ)` on `ℓ²(I, H)`. -/
def diagonalFormation (a : I → ℂ) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => H) 2 :=
  weightedInduction a (ContinuousLinearMap.id ℂ H) (fun _ => LinearIsometryEquiv.refl ℂ H)
    (fun _ => LinearIsometryEquiv.refl ℂ H) hbdd

omit [CompleteSpace H] in
theorem diagonalFormation_apply (a : I → ℂ) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (x : lp (fun _ : I => H) 2) (i : I) :
    (diagonalFormation a hbdd x : ∀ _ : I, H) i = a i • (x : ∀ _ : I, H) i := rfl

omit [Nonempty I] in
/-- With all amplitudes nonzero, the coordinatewise inverse amplitudes are bounded exactly when the
amplitudes have a uniform positive lower bound. -/
theorem bddAbove_inv_amp_iff {a : I → ℂ} (ha : ∀ i, a i ≠ 0) :
    BddAbove (Set.range fun i => ‖(a i)⁻¹‖) ↔ ∃ α > 0, ∀ i, α ≤ ‖a i‖ := by
  constructor
  · rintro ⟨M, hM⟩
    have hM' : ∀ i, ‖a i‖⁻¹ ≤ M := fun i => by simpa [norm_inv] using hM ⟨i, rfl⟩
    have hMpos : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨(max M 1)⁻¹, inv_pos.mpr hMpos, fun i => ?_⟩
    have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    rw [inv_le_comm₀ hMpos hai]
    exact (hM' i).trans (le_max_left _ _)
  · rintro ⟨α, hα, h⟩
    refine ⟨α⁻¹, ?_⟩
    rintro _ ⟨i, rfl⟩
    simp only [norm_inv]
    exact inv_anti₀ hα (h i)

omit [CompleteSpace H] in
/-- **Corollary 11.2, `(WOI.17)`.**  The diagonal formation has a bounded coefficient-faithful
left inverse exactly when `inf |aᵢ| > 0`. -/
theorem exists_leftInverse_diagonalFormation_iff [Nontrivial H] (a : I → ℂ)
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    (∃ L : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => H) 2,
        L.comp (diagonalFormation a hbdd) = ContinuousLinearMap.id ℂ _)
      ↔ ∃ α > 0, ∀ i, α ≤ ‖a i‖ := by
  classical
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hkey : ∀ i, 1 ≤ ‖L‖ * ‖a i‖ := by
      intro i
      have h := norm_le_norm_leftInverse_mul hL (lp.single 2 i v : lp (fun _ : I => H) 2)
      have hs : ‖(lp.single 2 i v : lp (fun _ : I => H) 2)‖ = ‖v‖ :=
        lp.norm_single (E := fun _ : I => H) (by norm_num) i v
      have hAs : ‖diagonalFormation a hbdd (lp.single 2 i v)‖ = ‖a i‖ * ‖v‖ := by
        have := norm_weightedInduction_escapeAt a (ContinuousLinearMap.id ℂ H)
          (fun _ => LinearIsometryEquiv.refl ℂ H) (fun _ => LinearIsometryEquiv.refl ℂ H) hbdd v i
        simpa [escapeAt, diagonalFormation] using this
      rw [hs, hAs] at h
      have h' : 1 * ‖v‖ ≤ (‖L‖ * ‖a i‖) * ‖v‖ := by nlinarith
      exact le_of_mul_le_mul_right h' hvpos
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have hLpos : 0 < ‖L‖ := by
      rcases eq_or_lt_of_le (norm_nonneg L) with h0 | h0
      · have := hkey i₀
        rw [← h0, zero_mul] at this
        exact absurd this (by norm_num)
      · exact h0
    refine ⟨‖L‖⁻¹, inv_pos.mpr hLpos, fun i => ?_⟩
    rw [inv_le_iff_one_le_mul₀ hLpos, mul_comm]
    exact hkey i
  · rintro ⟨α, hα, h⟩
    have ha : ∀ i, a i ≠ 0 := fun i hi => by
      have := h i
      rw [hi, norm_zero] at this
      linarith
    refine ⟨diagonalFormation (fun i => (a i)⁻¹) ((bddAbove_inv_amp_iff ha).mpr ⟨α, hα, h⟩), ?_⟩
    refine ContinuousLinearMap.ext fun x => ?_
    ext i
    show (a i)⁻¹ • (a i • (x : ∀ _ : I, H) i) = (x : ∀ _ : I, H) i
    rw [smul_smul, inv_mul_cancel₀ (ha i), one_smul]

omit [Nonempty I] [CompleteSpace H] in
theorem not_finiteDimensional_lp [Infinite I] [DecidableEq I] [Nontrivial H] :
    ¬ FiniteDimensional ℂ (lp (fun _ : I => H) 2) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u : H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos),
      inv_mul_cancel₀ hvpos.ne']
  exact not_finiteDimensional_of_orthonormal _
    (orthonormal_lp_single_const (Infinite.natEmbedding I) (fun _ => u) fun _ => hu1)

/-- A compact operator on an infinite-dimensional space has no bounded left inverse. -/
theorem not_exists_leftInverse_of_isCompactOperator {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hE : ¬ FiniteDimensional ℂ E) {T : E →L[ℂ] F} (hT : IsCompactOperator T) :
    ¬ ∃ L : F →L[ℂ] E, L.comp T = ContinuousLinearMap.id ℂ E := by
  rintro ⟨L, hL⟩
  have hc : IsCompactOperator (L.comp T) := hT.clm_comp L
  rw [hL] at hc
  exact hE (FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ) hc)

/-- **`(WOI.18)`.**  Compact or Schatten regularization of an infinite orbit has no bounded
coefficient-faithful decoder. -/
theorem not_exists_decoder_weightedInduction [Infinite I] [DecidableEq I] [Nontrivial H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hreg : IsCompactOperator (weightedInduction a D U V hbdd)
      ∨ ∃ p : ℝ, 0 < p ∧ MemRectSchattenClass p (weightedInduction a D U V hbdd)) :
    ¬ ∃ L : lp (fun _ : I => K) 2 →L[ℂ] lp (fun _ : I => H) 2,
        L.comp (weightedInduction a D U V hbdd) = ContinuousLinearMap.id ℂ _ := by
  have hc : IsCompactOperator (weightedInduction a D U V hbdd) := by
    rcases hreg with h | ⟨p, hp, h⟩
    · exact h
    · exact isCompactOperator_of_memRectSchattenClass hp h
  exact not_exists_leftInverse_of_isCompactOperator not_finiteDimensional_lp hc

omit [CompleteSpace H] in
/-- **Corollary 11.2.**  Every amplitude sequence that tends to zero over an infinite orbit destroys
bounded common recovery for the diagonal formation. -/
theorem not_exists_leftInverse_diagonalFormation_of_tendsto [Infinite I] [Nontrivial H]
    (a : I → ℂ) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : Tendsto a cofinite (𝓝 0)) :
    ¬ ∃ L : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => H) 2,
        L.comp (diagonalFormation a hbdd) = ContinuousLinearMap.id ℂ _ := by
  rw [exists_leftInverse_diagonalFormation_iff]
  rintro ⟨α, hα, h⟩
  rw [Metric.tendsto_nhds] at ha
  have hfin := ha α hα
  rw [Filter.eventually_cofinite] at hfin
  have huniv : {x : I | ¬ dist (a x) 0 < α} = Set.univ := by
    ext i
    simp only [Set.mem_setOf_eq, dist_zero_right, not_lt, Set.mem_univ, iff_true]
    exact h i
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

end Diagonal

end

end GaloisForLFunctions.HTGeometry
