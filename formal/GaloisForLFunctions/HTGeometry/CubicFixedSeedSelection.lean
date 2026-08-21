/-
# One deterministic cubic seed per system size

The squared positive part of the collision above `2/D` has ensemble mean at most `96/D³` against
every orthonormal basis, so its shell integral has the same bound after averaging over the seeds.
At least one seed is no worse than the average, and Markov applied to its positive-part square at
threshold `(κ/D)²` gives the collision tail for that single seed simultaneously at every `κ`.

Main results:
* `integrable_cubicPosPart` — the positive-part square is integrable on the shell.
* `exists_fixed_cubicSeed_integral_le` — **`(28)`**: one seed with small shell mean.
* `exists_fixed_cubicSeed_sphereLaw_le` — **`(26)`**.
* `exists_fixed_cubicSeed_limsup_le` — the fixed-seed form of `(17)`.
-/
import GaloisForLFunctions.HTGeometry.CubicSeedPlateauLaw

open Finset MeasureTheory Matrix Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The squared positive part of the shell collision of a cubic seed above `2/D`. -/
def cubicPosPart (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8)
    (x : coeffSphere (Fintype.card (ChainLabel (k + 3)))) : ℝ :=
  (max (crossCollision (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c) x
    - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0) ^ 2

theorem continuousOn_cubicPosPart (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8) :
    ContinuousOn (cubicPosPart k c) (simpleLocus (chainPauliFin_isHermitian (k + 3))) := by
  have hcont : Continuous (fun t : ℝ =>
      (max (t - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0) ^ 2) :=
    ((continuous_id.sub continuous_const).max continuous_const).pow 2
  exact hcont.comp_continuousOn (continuousOn_crossCollision
    (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c))

theorem ae_mem_simpleLocus (k : ℕ) :
    ∀ᵐ x ∂(sphereLaw (Fintype.card (ChainLabel (k + 3)))),
      x ∈ simpleLocus (chainPauliFin_isHermitian (k + 3)) :=
  MeasureTheory.ae_iff.mpr (sphereLaw_simpleLocus_compl k)

theorem aestronglyMeasurable_cubicPosPart (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8) :
    AEStronglyMeasurable (cubicPosPart k c)
      (sphereLaw (Fintype.card (ChainLabel (k + 3)))) := by
  have h := (continuousOn_cubicPosPart k c).aestronglyMeasurable
    (isOpen_simpleLocus (chainPauliFin_isHermitian (k + 3))).measurableSet
    (μ := sphereLaw (Fintype.card (ChainLabel (k + 3))))
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_simpleLocus k)] at h

/-- On the simple locus the collision of a cubic seed is bounded by the register dimension. -/
theorem cubicPosPart_le (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8)
    {x : coeffSphere (Fintype.card (ChainLabel (k + 3)))}
    (hx : x ∈ simpleLocus (chainPauliFin_isHermitian (k + 3))) :
    cubicPosPart k c x ≤ (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 2 := by
  have horth := orth_registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x
  have he : ∀ j, (∑ a, ‖registerEigenBasis (k + 3)
      (chainPauliFin_isHermitian (k + 3)) x j a‖ ^ 2) ≤ 1 :=
    fun j => le_of_eq (sum_normSq_of_orthonormal horth j)
  have hbound := phaseCollision_le_card
    (registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x) he
    (eighthPhase (polyEval 3 c))
  rw [cubicPosPart, crossCollision_cubicSeed k c hx]
  have hDnn : (0 : ℝ) ≤ (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) :=
    Nat.cast_nonneg _
  have hdiv : (0 : ℝ) ≤ 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) := by
    positivity
  have hmax : max (phaseCollision (registerEigenBasis (k + 3)
        (chainPauliFin_isHermitian (k + 3)) x) (eighthPhase (polyEval 3 c))
      - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0
      ≤ (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) := by
    refine max_le ?_ hDnn
    linarith [hbound, hdiv]
  have hnn : (0 : ℝ) ≤ max (phaseCollision (registerEigenBasis (k + 3)
        (chainPauliFin_isHermitian (k + 3)) x) (eighthPhase (polyEval 3 c))
      - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0 := le_max_right _ _
  exact pow_le_pow_left₀ hnn hmax 2

theorem integrable_cubicPosPart (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8) :
    Integrable (cubicPosPart k c) (sphereLaw (Fintype.card (ChainLabel (k + 3)))) := by
  have hNne : Nonempty (Fin (Fintype.card (ChainLabel (k + 3)))) :=
    instNonemptyChainCoordinate (k + 2)
  have hN : 0 < Fintype.card (ChainLabel (k + 3)) := Fin.pos_iff_nonempty.mpr hNne
  haveI := isProbabilityMeasure_sphereLaw hN
  refine Integrable.mono' (integrable_const
    ((Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 2))
    (aestronglyMeasurable_cubicPosPart k c) ?_
  filter_upwards [ae_mem_simpleLocus k] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [cubicPosPart]; positivity)]
  exact cubicPosPart_le k c hx


/-- **`(28)`.**  Averaged over the seed ensemble, the shell mean of the positive-part square is at
most `96/D³`. -/
theorem sum_integral_cubicPosPart_le (k : ℕ) :
    ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
        ∫ x, cubicPosPart k c x ∂(sphereLaw (Fintype.card (ChainLabel (k + 3))))
      ≤ ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ℝ) *
          (96 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 3) := by
  classical
  have hNne : Nonempty (Fin (Fintype.card (ChainLabel (k + 3)))) :=
    instNonemptyChainCoordinate (k + 2)
  have hN : 0 < Fintype.card (ChainLabel (k + 3)) := Fin.pos_iff_nonempty.mpr hNne
  haveI := isProbabilityMeasure_sphereLaw hN
  have hNs : (0 : ℝ) < ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ℝ) := by
    have : 0 < Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) := Fintype.card_pos
    exact_mod_cast this
  have hswap : ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
      ∫ x, cubicPosPart k c x ∂(sphereLaw (Fintype.card (ChainLabel (k + 3))))
      = ∫ x, ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8, cubicPosPart k c x
        ∂(sphereLaw (Fintype.card (ChainLabel (k + 3)))) :=
    (integral_finsetSum _ fun c _ => integrable_cubicPosPart k c).symm
  rw [hswap]
  have hint : Integrable (fun x => ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8, cubicPosPart k c x)
      (sphereLaw (Fintype.card (ChainLabel (k + 3)))) :=
    integrable_finsetSum _ fun c _ => integrable_cubicPosPart k c
  refine le_trans (integral_mono_ae hint (integrable_const
    (((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ℝ) *
      (96 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 3))) ?_) ?_
  · filter_upwards [ae_mem_simpleLocus k] with x hx
    have horth := orth_registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x
    have hbase := sum_posPart_sq_phaseCollision_polyEval_le (ι := Fin (k + 3))
      (J := FiniteQubitConfiguration (Fin (k + 3))) 3 (by norm_num)
      (registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x) horth rfl
    have hpt : ∀ c : MonLe (Fin (k + 3)) 3 → ZMod 8, cubicPosPart k c x
        = (max (phaseCollision (registerEigenBasis (k + 3)
            (chainPauliFin_isHermitian (k + 3)) x) (eighthPhase (polyEval 3 c))
          - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0) ^ 2 := by
      intro c
      rw [cubicPosPart, crossCollision_cubicSeed k c hx]
    rw [Finset.sum_congr rfl (fun c _ => hpt c)]
    rw [← div_le_iff₀' hNs]
    calc (∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
          (max (phaseCollision (registerEigenBasis (k + 3)
            (chainPauliFin_isHermitian (k + 3)) x) (eighthPhase (polyEval 3 c))
          - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0) ^ 2)
          / ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ℝ)
        = ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ℝ)⁻¹ *
          ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
            (max (phaseCollision (registerEigenBasis (k + 3)
              (chainPauliFin_isHermitian (k + 3)) x) (eighthPhase (polyEval 3 c))
            - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0) ^ 2 := by
          rw [div_eq_inv_mul]
      _ ≤ _ := hbase
  · rw [integral_const, probReal_univ, one_smul]

/-- **One seed is no worse than the average.** -/
theorem exists_fixed_cubicSeed_integral_le (k : ℕ) :
    ∃ c₀ : MonLe (Fin (k + 3)) 3 → ZMod 8,
      ∫ x, cubicPosPart k c₀ x ∂(sphereLaw (Fintype.card (ChainLabel (k + 3))))
        ≤ 96 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 3 := by
  classical
  have hne : (Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)).Nonempty :=
    Finset.univ_nonempty (α := MonLe (Fin (k + 3)) 3 → ZMod 8)
  have hsum := sum_integral_cubicPosPart_le k
  have hconst : ∑ _c : MonLe (Fin (k + 3)) 3 → ZMod 8,
      (96 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 3)
      = ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ℝ) *
        (96 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 3) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hkey : ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
        (∫ x, cubicPosPart k c x ∂(sphereLaw (Fintype.card (ChainLabel (k + 3)))))
      ≤ ∑ _c : MonLe (Fin (k + 3)) 3 → ZMod 8,
        (96 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) ^ 3) := by
    rw [hconst]
    exact hsum
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_le_of_sum_le hne hkey
  exact ⟨c₀, hc₀⟩


/-- **`(26)`.**  One cubic seed can be fixed in advance so that, simultaneously for every `κ > 0`,
the shell mass of the Hamiltonians against which its collision exceeds `(2+κ)/D` is at most
`96/(κ²D)`. -/
theorem exists_fixed_cubicSeed_sphereLaw_le (k : ℕ) :
    ∃ c₀ : MonLe (Fin (k + 3)) 3 → ZMod 8, ∀ kap : ℝ, 0 < kap →
      (sphereLaw (Fintype.card (ChainLabel (k + 3))))
          (goodSet (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c₀)
            ((2 + kap) / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)))ᶜ
        ≤ ENNReal.ofReal (96 /
            (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))) := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_fixed_cubicSeed_integral_le k
  refine ⟨c₀, fun kap hkap => ?_⟩
  have hNne : Nonempty (Fin (Fintype.card (ChainLabel (k + 3)))) :=
    instNonemptyChainCoordinate (k + 2)
  have hN : 0 < Fintype.card (ChainLabel (k + 3)) := Fin.pos_iff_nonempty.mpr hNne
  haveI := isProbabilityMeasure_sphereLaw hN
  have hDR : (0 : ℝ) < (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) := by
    have : 0 < Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) := Fintype.card_pos
    exact_mod_cast this
  have hthr : (0 : ℝ) < kap / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) := by
    positivity
  have hsub : (goodSet (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c₀)
        ((2 + kap) / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)))ᶜ
      ⊆ (simpleLocus (chainPauliFin_isHermitian (k + 3)))ᶜ ∪
        {x | (kap / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) ^ 2
          ≤ cubicPosPart k c₀ x} := by
    intro x hx
    by_cases hxs : x ∈ simpleLocus (chainPauliFin_isHermitian (k + 3))
    · refine Or.inr ?_
      have hgt : (2 + kap) / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)
          < crossCollision (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c₀) x := by
        by_contra hle
        exact hx ⟨hxs, not_lt.mp hle⟩
      rw [collision_threshold_split (ne_of_gt hDR)] at hgt
      have hmax : kap / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)
          ≤ max (crossCollision (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c₀) x
            - 2 / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) 0 :=
        le_trans (by linarith [hgt]) (le_max_left _ _)
      show (kap / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) ^ 2
        ≤ cubicPosPart k c₀ x
      rw [cubicPosPart]
      exact pow_le_pow_left₀ hthr.le hmax 2
    · exact Or.inl hxs
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [sphereLaw_simpleLocus_compl k, zero_add]
  have hnn : (0 : coeffSphere (Fintype.card (ChainLabel (k + 3))) → ℝ)
      ≤ᵐ[sphereLaw (Fintype.card (ChainLabel (k + 3)))] cubicPosPart k c₀ :=
    Filter.Eventually.of_forall fun x => by
      show (0 : ℝ) ≤ cubicPosPart k c₀ x
      rw [cubicPosPart]
      positivity
  have hmark := mul_meas_ge_le_integral_of_nonneg hnn (integrable_cubicPosPart k c₀)
    ((kap / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) ^ 2)
  have hreal : (sphereLaw (Fintype.card (ChainLabel (k + 3)))).real
      {x | (kap / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) ^ 2
        ≤ cubicPosPart k c₀ x}
      ≤ 96 / (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) := by
    have hsq : (0 : ℝ) < (kap / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) ^ 2 :=
      by positivity
    rw [← collision_tail_scale hDR hkap, le_div_iff₀ hsq, mul_comm]
    exact le_trans hmark hc₀
  rw [← ENNReal.ofReal_toReal (measure_ne_top
    (sphereLaw (Fintype.card (ChainLabel (k + 3)))) _), ← measureReal_def]
  exact ENNReal.ofReal_le_ofReal hreal


/-- **The fixed-seed form of `(17)`.**  For one seed fixed in advance, the long-time shell density
of the directions whose evolution reaches the dictionary is at most `2^{-r/2} + 96/(κ²D)`, with the
probability taken over the single Hamiltonian draw only. -/
theorem exists_fixed_cubicSeed_limsup_le (k : ℕ) :
    ∃ c₀ : MonLe (Fin (k + 3)) 3 → ZMod 8,
      ∀ {C : Type} [Fintype C] [Nonempty C]
        (Z : C → (Fin (2 ^ (k + 3)) → ℂ)), (∀ κ, finiteComplexInner (Z κ) (Z κ) = 1) →
        ∀ {a : ℝ}, 0 < a → ∀ {r : ℕ}, 1 ≤ r → ∀ {kap : ℝ}, 0 < kap →
        16 * ((2 + kap) / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) / a ^ 2
            ≤ 1 / (2 * r) →
        ∀ {M : ℝ}, 1 < M → ∀ {s : ℕ}, (Fintype.card C : ℝ) ≤ M ^ (s + 1) →
        ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2 →
        (atTop.limsup fun t : ℝ => (sphereLaw (Fintype.card (ChainLabel (k + 3))))
            {x | ∃ κ : C, a ≤ finitePureStateFidelity
              (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
                (2 * Real.pi * t) *ᵥ cubicSeed (k + 3) c₀) (Z κ)})
          ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
            + ENNReal.ofReal (96 /
                (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))) := by
  obtain ⟨c₀, hc₀⟩ := exists_fixed_cubicSeed_sphereLaw_le k
  refine ⟨c₀, ?_⟩
  intro C _ _ Z hZ a ha r hr kap hkap hscale M hM s hcard hs
  exact le_trans (limsup_sphereLaw_seedCapture_le k ⟨0, Nat.two_pow_pos (k + 3)⟩ Z hZ
      (cubicSeed (k + 3) c₀)
    (finiteComplexInner_cubicSeed (k + 3) c₀) ha hr hscale hM hcard hs)
    (add_le_add le_rfl (hc₀ kap hkap))

end GaloisForLFunctions.HTGeometry

end
