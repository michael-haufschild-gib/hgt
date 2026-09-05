/-
# Cubic-phase seeds give full-scale static-local complexity plateaux

A cubic eighth-root phase seed read on the numbered register is a unit state whose collision with
the shell eigenbasis is the ensemble collision of the previous section, so the fixed-seed plateau
bound applies to every seed and the collision tail bounds the seed average of its failure term.
Averaging over the seed ensemble therefore costs `96/(κ²D)` once, and the long-time shell density of
the directions reaching a finite dictionary is at most `2^{-r/2} + 96/(κ²D)`.

Main results:
* `crossCollision_cubicSeed` — the shell collision of a cubic seed is its ensemble collision.
* `sphereLaw_simpleLocus_compl` — the degenerate shell directions are null.
* `sum_sphereLaw_cubicSeed_goodSet_compl_le`,
  `sphereLaw_cubicSeed_goodSet_compl_average_le` — **`(24)`**.
* `limsup_sphereLaw_cubicSeeded_sum_le`, `limsup_sphereLaw_cubicSeeded_le` — **`(17)`**.
-/
import GaloisForLFunctions.HTGeometry.StabilizerSeededPlateauLaw
import GaloisForLFunctions.HTGeometry.CubicSeedCollisionTail

open Finset MeasureTheory Matrix Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem finitePureStateFidelity_comm (ψ φ : α → ℂ) :
    finitePureStateFidelity ψ φ = finitePureStateFidelity φ ψ := by
  rw [finitePureStateFidelity, finitePureStateFidelity, finiteComplexInner_conj_symm ψ φ,
    Complex.norm_conj]

theorem phaseCollision_eq_sum_fidelity {ι : Type*} [Fintype ι] (e : ι → α → ℂ) (x : α → ℝ) :
    phaseCollision e x = ∑ j, finitePureStateFidelity (e j) (uniformPhaseSeed x) ^ 2 := by
  rw [phaseCollision]
  exact Finset.sum_congr rfl fun j _ => by
    rw [finitePureStateFidelity_comm (uniformPhaseSeed x) (e j)]

theorem sum_normSq_uniformPhaseSeed (hD : 0 < Fintype.card α) (x : α → ℝ) :
    (∑ a, ‖uniformPhaseSeed x a‖ ^ 2) = 1 := by
  have hDR : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hD
  have hterm : ∀ a : α, ‖uniformPhaseSeed x a‖ ^ 2 = ((Fintype.card α : ℝ))⁻¹ := by
    intro a
    rw [uniformPhaseSeed, torusReplicaPhaseOrbit, norm_mul, norm_charLift, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (uniformPhaseWeights_nonneg a)]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hDR)]


/-- A cubic eighth-root phase seed read on the numbered register. -/
def cubicSeed (n : ℕ) (c : MonLe (Fin n) 3 → ZMod 8) : Fin (2 ^ n) → ℂ :=
  fun m => uniformPhaseSeed (eighthPhase (polyEval 3 c)) ((qubitConfigFin n).symm m)

theorem cubicSeed_comp (n : ℕ) (c : MonLe (Fin n) 3 → ZMod 8) :
    (fun y => cubicSeed n c ((qubitConfigFin n) y))
      = uniformPhaseSeed (eighthPhase (polyEval 3 c)) := by
  funext y
  show uniformPhaseSeed (eighthPhase (polyEval 3 c))
      ((qubitConfigFin n).symm ((qubitConfigFin n) y)) = _
  rw [Equiv.symm_apply_apply]

theorem finiteComplexInner_cubicSeed (n : ℕ) (c : MonLe (Fin n) 3 → ZMod 8) :
    finiteComplexInner (cubicSeed n c) (cubicSeed n c) = 1 := by
  have hcardpos : 0 < Fintype.card (FiniteQubitConfiguration (Fin n)) := Fintype.card_pos
  have hq := sum_normSq_uniformPhaseSeed hcardpos (eighthPhase (polyEval 3 c))
  have hs1 : ∑ m, ‖cubicSeed n c m‖ ^ 2 = 1 := by
    rw [← hq]
    exact Equiv.sum_comp (qubitConfigFin n).symm
      (fun y => ‖uniformPhaseSeed (eighthPhase (polyEval 3 c)) y‖ ^ 2)
  have hcast : finiteComplexInner (cubicSeed n c) (cubicSeed n c)
      = ((∑ m, ‖cubicSeed n c m‖ ^ 2 : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [hcast, hs1]
  norm_num

theorem crossCollision_cubicSeed (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8)
    {x : coeffSphere (Fintype.card (ChainLabel (k + 3)))}
    (hx : x ∈ simpleLocus (chainPauliFin_isHermitian (k + 3))) :
    crossCollision (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c) x
      = phaseCollision (registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x)
          (eighthPhase (polyEval 3 c)) := by
  rw [crossCollision_eq (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c) hx]
  rw [← spectralCollision_reindexBasis (qubitConfigFin (k + 3))
    (sortedEigenBasis (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x))
    (cubicSeed (k + 3) c)]
  rw [cubicSeed_comp, phaseCollision_eq_sum_fidelity]
  rfl

theorem orth_registerEigenBasis (n : ℕ) {N : ℕ} {P : Fin N → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (x : coeffSphere N) (j l : FiniteQubitConfiguration (Fin n)) :
    finiteComplexInner (registerEigenBasis n hP x j) (registerEigenBasis n hP x l)
      = if j = l then 1 else 0 := by
  have heb := isOrthoEigenBasis_sortedEigenBasis hP (sphereCoeff x)
  have hinner : finiteComplexInner (registerEigenBasis n hP x j) (registerEigenBasis n hP x l)
      = finiteComplexInner (sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n j))
        (sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n l)) := by
    rw [finiteComplexInner, finiteComplexInner]
    exact Equiv.sum_comp (qubitConfigFin n)
      (fun m => (starRingEnd ℂ) (sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n j) m) *
        sortedEigenBasis hP (sphereCoeff x) (qubitConfigFin n l) m)
  rw [hinner, heb.orth]
  by_cases h : j = l
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hc => h ((qubitConfigFin n).injective hc))]


/-- The degenerate directions of the nearest-neighbour Pauli shell are null. -/
theorem sphereLaw_simpleLocus_compl (k : ℕ) :
    (sphereLaw (Fintype.card (ChainLabel (k + 3))))
        (simpleLocus (chainPauliFin_isHermitian (k + 3)))ᶜ = 0 := by
  have hcompl : (simpleLocus (chainPauliFin_isHermitian (k + 3)))ᶜ = sphereCoeff ⁻¹' {θ |
      ¬ Function.Injective (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} := rfl
  rw [hcompl]
  exact sphereLaw_eq_zero_of_toSphere_eq_zero
    (toSphere_degenerate_eq_zero (chainPauliFin_isHermitian (k + 3))
      (spectralDiscriminantPoly_chainPauliFin_succ_ne_zero k))

/-- **`(24)` in summed form.**  Summed over the cubic eighth-root phase seeds, the shell mass of the
directions failing the collision cap `(2+κ)/D` is at most `|P₃| · 96/(κ²D)`. -/
theorem sum_sphereLaw_cubicSeed_goodSet_compl_le (k : ℕ) {kap : ℝ} (hkap : 0 < kap) :
    ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
        (sphereLaw (Fintype.card (ChainLabel (k + 3))))
          (goodSet (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c)
            ((2 + kap) / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)))ᶜ
      ≤ ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal)
          * ENNReal.ofReal (96 /
            (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))) := by
  classical
  obtain ⟨hPP, hPPdef⟩ : ∃ hPP, hPP = chainPauliFin_isHermitian (k + 3) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = (2 + kap) /
    (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ) := ⟨_, rfl⟩
  have hNne : Nonempty (Fin (Fintype.card (ChainLabel (k + 3)))) :=
    instNonemptyChainCoordinate (k + 2)
  have hN : 0 < Fintype.card (ChainLabel (k + 3)) := Fin.pos_iff_nonempty.mpr hNne
  haveI := isProbabilityMeasure_sphereLaw hN
  rw [← hPPdef, ← hc₀def]
  obtain ⟨badSet, hbadDef⟩ : ∃ badSet : (MonLe (Fin (k + 3)) 3 → ZMod 8) →
      Set (coeffSphere (Fintype.card (ChainLabel (k + 3)))),
      badSet = fun c => simpleLocus hPP ∩
        crossCollision hPP (cubicSeed (k + 3) c) ⁻¹' Set.Ioi c₀ := ⟨_, rfl⟩
  have hbadmeas : ∀ c, MeasurableSet (badSet c) := by
    intro c
    rw [hbadDef]
    exact ((continuousOn_crossCollision hPP (cubicSeed (k + 3) c)).isOpen_inter_preimage
      (isOpen_simpleLocus hPP) isOpen_Ioi).measurableSet
  have hSnull : (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (simpleLocus hPP)ᶜ = 0 := by
    rw [hPPdef]
    exact sphereLaw_simpleLocus_compl k
  have hstep : ∀ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
      (sphereLaw (Fintype.card (ChainLabel (k + 3))))
          (goodSet hPP (cubicSeed (k + 3) c) c₀)ᶜ
        ≤ (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (badSet c) := by
    intro c
    have hsub : (goodSet hPP (cubicSeed (k + 3) c) c₀)ᶜ ⊆ (simpleLocus hPP)ᶜ ∪ badSet c := by
      intro x hx
      by_cases hxs : x ∈ simpleLocus hPP
      · refine Or.inr ?_
        rw [hbadDef]
        refine ⟨hxs, ?_⟩
        show c₀ < crossCollision hPP (cubicSeed (k + 3) c) x
        by_contra hle
        exact hx ⟨hxs, not_lt.mp hle⟩
      · exact Or.inl hxs
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [hSnull, zero_add]
  refine le_trans (Finset.sum_le_sum (fun c _ => hstep c)) ?_
  have hind : ∀ c, (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (badSet c)
      = ∫⁻ x, Set.indicator (badSet c)
          (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x
        ∂(sphereLaw (Fintype.card (ChainLabel (k + 3)))) :=
    fun c => (lintegral_indicator_one (hbadmeas c)).symm
  rw [Finset.sum_congr rfl (fun c _ => hind c), ← lintegral_finsetSum]
  · refine le_trans (lintegral_mono
      (g := fun _ => ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal) *
        ENNReal.ofReal (96 /
          (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)))) ?_) ?_
    · intro x
      show (∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8, Set.indicator (badSet c)
          (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x)
        ≤ _
      have hcount : (∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
          Set.indicator (badSet c)
            (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x)
          = (((Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)).filter
              fun c => x ∈ badSet c).card : ENNReal) := by
        rw [Finset.sum_congr rfl (fun c _ => by
          rw [Set.indicator_apply] : ∀ c ∈ (Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)),
            Set.indicator (badSet c)
              (fun _ : coeffSphere (Fintype.card (ChainLabel (k + 3))) => (1 : ENNReal)) x
              = if x ∈ badSet c then (1 : ENNReal) else 0)]
        rw [Finset.sum_boole]
      rw [hcount]
      by_cases hxs : x ∈ simpleLocus hPP
      · have hfilter : ((Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)).filter
            fun c => x ∈ badSet c)
            = (Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)).filter
              fun c => (2 + kap) /
                (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)
                < phaseCollision (registerEigenBasis (k + 3) hPP x)
                    (eighthPhase (polyEval 3 c)) := by
          refine Finset.filter_congr fun c _ => ?_
          rw [hbadDef]
          have hcc : crossCollision hPP (cubicSeed (k + 3) c) x
              = phaseCollision (registerEigenBasis (k + 3) hPP x)
                  (eighthPhase (polyEval 3 c)) := by
            rw [hPPdef]
            exact crossCollision_cubicSeed k c (by rw [hPPdef] at hxs; exact hxs)
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, hxs, true_and, hcc,
            hc₀def]
        rw [hfilter]
        have horth := orth_registerEigenBasis (k + 3) hPP x
        have htail := card_filter_phaseCollision_polyEval_gt_le (ι := Fin (k + 3))
          (J := FiniteQubitConfiguration (Fin (k + 3))) 3 (by norm_num)
          (registerEigenBasis (k + 3) hPP x) horth rfl hkap
        have hNpos : (0 : ℝ) < (Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℝ) := by
          have : 0 < Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) := Fintype.card_pos
          exact_mod_cast this
        have hle : (((Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)).filter
              fun c => (2 + kap) /
                (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)
                < phaseCollision (registerEigenBasis (k + 3) hPP x)
                    (eighthPhase (polyEval 3 c))).card : ℝ)
            ≤ ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ℝ) *
              (96 / (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))) := by
          rw [mul_comm, ← div_le_iff₀ hNpos, div_eq_mul_inv]
          exact htail
        have hE := ENNReal.ofReal_le_ofReal hle
        rw [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast] at hE
        exact hE
      · have hempty : ((Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)).filter
            fun c => x ∈ badSet c) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr fun c _ => ?_
          rw [hbadDef]
          intro hcon
          exact hxs hcon.1
        rw [hempty]
        simp
    · rw [lintegral_const, measure_univ, mul_one]
  · intro c _
    exact (measurable_const.indicator (hbadmeas c))

/-- **`(17)` in summed form.**  Summed over the cubic eighth-root phase seeds, the long-time shell
density of the directions whose evolution reaches the dictionary is at most
`|P₃| (2^{-r/2} + 96/(κ²D))`. -/
theorem limsup_sphereLaw_cubicSeeded_sum_le (k : ℕ) {C : Type*} [Fintype C] [Nonempty C]
    (i₀ : Fin (2 ^ (k + 3)))
    (Z : C → (Fin (2 ^ (k + 3)) → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {kap : ℝ} (hkap : 0 < kap)
    (hscale : 16 * ((2 + kap) /
        (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (atTop.limsup fun t : ℝ => ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
          (sphereLaw (Fintype.card (ChainLabel (k + 3))))
            {x | ∃ κ : C, a ≤ finitePureStateFidelity
              (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
                (2 * Real.pi * t) *ᵥ cubicSeed (k + 3) c) (Z κ)})
      ≤ ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal)
            * ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
        + ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal)
            * ENNReal.ofReal (96 /
              (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))) := by
  classical
  refine le_trans (limsup_finsetSum_le (Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8))
    (fun c t => (sphereLaw (Fintype.card (ChainLabel (k + 3))))
      {x | ∃ κ : C, a ≤ finitePureStateFidelity
        (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
          (2 * Real.pi * t) *ᵥ cubicSeed (k + 3) c) (Z κ)})) ?_
  have hper : ∀ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
      (atTop.limsup fun t : ℝ => (sphereLaw (Fintype.card (ChainLabel (k + 3))))
        {x | ∃ κ : C, a ≤ finitePureStateFidelity
          (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
            (2 * Real.pi * t) *ᵥ cubicSeed (k + 3) c) (Z κ)})
        ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
          + (sphereLaw (Fintype.card (ChainLabel (k + 3))))
              (goodSet (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c)
                ((2 + kap) /
                  (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)))ᶜ :=
    fun c => limsup_sphereLaw_seedCapture_le k i₀ Z hZ (cubicSeed (k + 3) c)
      (finiteComplexInner_cubicSeed (k + 3) c) ha hr hscale hM hcard hs
  refine le_trans (Finset.sum_le_sum (fun c _ => hper c)) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  exact add_le_add le_rfl (sum_sphereLaw_cubicSeed_goodSet_compl_le k hkap)

theorem limsup_const_mul_atTop (c : ENNReal) (hc : c ≠ ⊤) (u : ℝ → ENNReal) :
    atTop.limsup (fun t => c * u t) = c * atTop.limsup u := by
  have hmono : Monotone (fun x : ENNReal => c * x) := fun a b hab => mul_le_mul' le_rfl hab
  exact (hmono.map_limsup_of_continuousAt u
    ((ENNReal.continuous_const_mul hc).continuousAt)).symm

/-- **`(17)`.**  The joint seed-and-shell probability of reaching the dictionary at a common late
time is at most `96/(κ²D) + 2^{-r/2}`. -/
theorem limsup_sphereLaw_cubicSeeded_le (k : ℕ) {C : Type*} [Fintype C] [Nonempty C]
    (i₀ : Fin (2 ^ (k + 3)))
    (Z : C → (Fin (2 ^ (k + 3)) → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {kap : ℝ} (hkap : 0 < kap)
    (hscale : 16 * ((2 + kap) /
        (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (atTop.limsup fun t : ℝ =>
        ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal)⁻¹ *
          ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
            (sphereLaw (Fintype.card (ChainLabel (k + 3))))
              {x | ∃ κ : C, a ≤ finitePureStateFidelity
                (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
                  (2 * Real.pi * t) *ᵥ cubicSeed (k + 3) c) (Z κ)})
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
        + ENNReal.ofReal (96 /
            (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))) := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : ENNReal,
    N = ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal) := ⟨_, rfl⟩
  have hNtop : N ≠ ⊤ := by rw [hNdef]; exact ENNReal.natCast_ne_top _
  have hNzero : N ≠ 0 := by
    rw [hNdef, Ne, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  have hsum := limsup_sphereLaw_cubicSeeded_sum_le k i₀ Z hZ ha hr hkap hscale hM hcard hs
  rw [← hNdef] at hsum
  rw [← hNdef, limsup_const_mul_atTop N⁻¹ (ENNReal.inv_ne_top.mpr hNzero)]
  refine le_trans (mul_le_mul' le_rfl hsum) ?_
  rw [mul_add, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hNzero hNtop,
    one_mul, one_mul]


/-- **`(24)`.**  The joint seed-and-shell probability that the collision cap `(2+κ)/D` fails is at
most `96/(κ²D)`. -/
theorem sphereLaw_cubicSeed_goodSet_compl_average_le (k : ℕ) {kap : ℝ} (hkap : 0 < kap) :
    ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal)⁻¹ *
        ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
          (sphereLaw (Fintype.card (ChainLabel (k + 3))))
            (goodSet (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c)
              ((2 + kap) / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)))ᶜ
      ≤ ENNReal.ofReal (96 /
          (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))) := by
  obtain ⟨N, hNdef⟩ : ∃ N : ENNReal,
    N = ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℕ) : ENNReal) := ⟨_, rfl⟩
  have hNtop : N ≠ ⊤ := by rw [hNdef]; exact ENNReal.natCast_ne_top _
  have hNzero : N ≠ 0 := by
    rw [hNdef, Ne, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  have hsum := sum_sphereLaw_cubicSeed_goodSet_compl_le k hkap
  rw [← hNdef] at hsum ⊢
  refine le_trans (mul_le_mul' le_rfl hsum) ?_
  rw [← mul_assoc, ENNReal.inv_mul_cancel hNzero hNtop, one_mul]

end GaloisForLFunctions.HTGeometry

end
