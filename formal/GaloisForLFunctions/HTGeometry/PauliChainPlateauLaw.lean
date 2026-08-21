/-
# The fixed-shell plateau law on the nearest-neighbour Pauli shell

Instantiating the shell plateau bookkeeping at the card's own nearest-neighbour Pauli family and
feeding it the collision tail gives `(20)` unconditionally: for every finite gate dictionary below
the replica order, the long-time shell density of the coefficient directions whose evolution of
`|0…0⟩` reaches the dictionary is at most `2^{-r/2} + 1/L`.

Main results:
* `chainInput` — the all-zero product state on the numbered register.
* `spectralCollision_sortedEigenBasis_chain` — the collision is the one the shell tail bounds.
* `limsup_sphereLaw_chainCapture_le` — **`(20)` on the card's own ensemble**.
* `scale_of_replicaOrder`, `eventually_sphereLaw_chainCapture_le` — `(18)` and `(21)`.
-/
import GaloisForLFunctions.HTGeometry.ShellPlateauAssembly
import GaloisForLFunctions.HTGeometry.ChainShellCollisionBound
import GaloisForLFunctions.HTGeometry.PauliChainDephasing

open Filter Topology MeasureTheory Metric Matrix ComplexConjugate

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

/-- The all-zero product state read on the numbered register. -/
def chainInput (n : ℕ) : Fin (2 ^ n) → ℂ :=
  fun m => zeroProductState (Fin n) ((qubitConfigFin n).symm m)

theorem finiteComplexInner_chainInput (n : ℕ) :
    finiteComplexInner (chainInput n) (chainInput n) = 1 := by
  have hsum : ∑ m, ‖chainInput n m‖ ^ 2 = 1 := by
    rw [← sum_normSq_zeroProductState (Fin n)]
    exact Equiv.sum_comp (qubitConfigFin n).symm
      (fun x => ‖zeroProductState (Fin n) x‖ ^ 2)
  have hcast : finiteComplexInner (chainInput n) (chainInput n)
      = ((∑ m, ‖chainInput n m‖ ^ 2 : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [hcast, hsum]
  norm_num

/-! ## The collision functional in the two labellings -/

theorem spectralCollision_reindexBasis {α β : Type*} [Fintype α] [Fintype β]
    (σ : α ≃ β) (E : β → β → ℂ) (ψ : β → ℂ) :
    spectralCollision (fun j x => E (σ j) (σ x)) (fun x => ψ (σ x))
      = spectralCollision E ψ := by
  classical
  have hinner : ∀ j : α, finiteComplexInner (fun x => E (σ j) (σ x)) (fun x => ψ (σ x))
      = finiteComplexInner (E (σ j)) ψ := by
    intro j
    rw [finiteComplexInner, finiteComplexInner]
    exact Equiv.sum_comp σ (fun y => (starRingEnd ℂ) (E (σ j) y) * ψ y)
  rw [spectralCollision, spectralCollision]
  rw [← Equiv.sum_comp σ (fun b => finitePureStateFidelity (E b) ψ ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finitePureStateFidelity, finitePureStateFidelity, hinner j]

theorem spectralCollision_permuteBasis {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (E : α → α → ℂ) (ψ : α → ℂ) :
    spectralCollision (fun j => E (σ j)) ψ = spectralCollision E ψ := by
  rw [spectralCollision, spectralCollision]
  exact Equiv.sum_comp σ (fun b => finitePureStateFidelity (E b) ψ ^ 2)

/-- **The collision of the sorted numbered eigenbasis is the collision of the register
eigenbasis.** -/
theorem spectralCollision_sortedEigenBasis_chain (n : ℕ)
    (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) :
    spectralCollision (sortedEigenBasis (chainPauliFin_isHermitian n) θ) (chainInput n)
      = spectralCollision
          (fun j x => hermitianEigenBasis (spectralEnsembleMatrix (chainPauliFin n) θ)
            (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ)
            (qubitConfigFin n j) (qubitConfigFin n x))
          (zeroProductState (Fin n)) := by
  rw [show sortedEigenBasis (chainPauliFin_isHermitian n) θ
      = fun j => (hermitianEigenBasis (spectralEnsembleMatrix (chainPauliFin n) θ)
        (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ))
        ((Tuple.sort (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ).eigenvalues)
          j) from rfl]
  rw [spectralCollision_permuteBasis]
  rw [← spectralCollision_reindexBasis (qubitConfigFin n)
    (hermitianEigenBasis (spectralEnsembleMatrix (chainPauliFin n) θ)
      (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ))
    (chainInput n)]
  congr 1
  funext x
  rw [chainInput]
  simp

/-! ## From the shell law to the sphere law -/

theorem shellProbability_eq_map_sphereLaw (N : ℕ) :
    shellProbability (Fin N) = Measure.map (sphereCoeff (N := N)) (sphereLaw N) := by
  rw [shellProbability, sphereLaw, Measure.map_smul, shellCoefficientMeasure_univ]
  rfl

theorem sphereLaw_preimage_eq (N : ℕ) {B : Set (Fin N → ℝ)} (hB : MeasurableSet B) :
    (sphereLaw N) (sphereCoeff ⁻¹' B) = (shellProbability (Fin N)) B := by
  rw [shellProbability_eq_map_sphereLaw N,
    Measure.map_apply continuous_sphereCoeff.measurable hB]

/-! ## The plateau law -/

theorem exists_balanced_nonzero_character (E : ℕ) (hE : 2 ≤ E) :
    ∃ kv : Fin E → ℝ, (∑ j, kv j = 0) ∧ kv ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin E, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin E, (j : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hij : i ≠ j := by
    intro h
    rw [h, hj] at hi
    omega
  refine ⟨(Pi.single i (1 : ℝ) : Fin E → ℝ) - (Pi.single j (1 : ℝ) : Fin E → ℝ), ?_, ?_⟩
  · simp
  · intro h0
    have hval := congrFun h0 i
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply,
      Pi.single_eq_of_ne hij] at hval
    exact absurd hval (by norm_num)

theorem spectralDiscriminantPoly_chainPauliFin_succ_ne_zero (k : ℕ) :
    spectralDiscriminantPoly (chainPauliFin (k + 3)) ≠ 0 := by
  obtain ⟨kv, hksum, hkne⟩ := exists_balanced_nonzero_character (2 ^ (k + 3)) (by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega))
  exact spectralDiscriminantPoly_chainPauliFin_ne_zero k hksum hkne

/-- **`(20)` on the card's own nearest-neighbour Pauli shell.**  For every finite target dictionary
below the replica order, the long-time shell density of the coefficient directions whose evolution
of the all-zero product state reaches the dictionary at fidelity `a` is at most
`2^{-r/2} + 1/L`. -/
theorem limsup_sphereLaw_chainCapture_le (k : ℕ)
    {C : Type*} [Fintype C] [Nonempty C]
    (i₀ : Fin (2 ^ (k + 3)))
    (Z : C → (Fin (2 ^ (k + 3)) → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {L : ℝ} (hL : 0 < L)
    (hscale : 16 * (L * (2 / 3 : ℝ) ^ (k + 3)) / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (atTop.limsup fun t : ℝ =>
        (sphereLaw (Fintype.card (ChainLabel (k + 3))))
          {x | ∃ κ : C, a ≤ finitePureStateFidelity
            (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
              (2 * Real.pi * t) *ᵥ chainInput (k + 3)) (Z κ)})
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) + ENNReal.ofReal (1 / L) := by
  classical
  have hNne : Nonempty (Fin (Fintype.card (ChainLabel (k + 3)))) :=
    instNonemptyChainCoordinate (k + 2)
  have hN : 0 < Fintype.card (ChainLabel (k + 3)) := Fin.pos_iff_nonempty.mpr hNne
  have hdisc := spectralDiscriminantPoly_chainPauliFin_succ_ne_zero k
  obtain ⟨hP, hPdef⟩ : ∃ hP, hP = chainPauliFin_isHermitian (k + 3) := ⟨_, rfl⟩
  obtain ⟨Om, hOmdef⟩ : ∃ Om, Om = chainInput (k + 3) := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = L * (2 / 3 : ℝ) ^ (k + 3) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G, G = goodSet hP Om c₀ := ⟨_, rfl⟩
  have hGmeas : MeasurableSet G := by
    rw [hGdef]; exact measurableSet_goodSet hP Om c₀
  have hGsimple : ∀ x ∈ G, Function.Injective
      (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues := by
    intro x hx
    rw [hGdef] at hx
    exact hx.1
  have hGcoll : ∀ x ∈ G, spectralCollision (sortedEigenBasis hP (sphereCoeff x)) Om ≤ c₀ := by
    intro x hx
    rw [hGdef] at hx
    rw [← crossCollision_eq hP Om hx.1]
    exact hx.2
  have hSnull : (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (simpleLocus hP)ᶜ = 0 := by
    have hcompl : (simpleLocus hP)ᶜ = sphereCoeff ⁻¹' {θ |
        ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := rfl
    rw [hcompl, hPdef]
    exact sphereLaw_eq_zero_of_toSphere_eq_zero
      (toSphere_degenerate_eq_zero (chainPauliFin_isHermitian (k + 3)) hdisc)
  have hbad : (sphereLaw (Fintype.card (ChainLabel (k + 3))))
      (sphereCoeff ⁻¹' {θ | c₀ ≤ spectralCollision
        (fun j x => hermitianEigenBasis (spectralEnsembleMatrix (chainPauliFin (k + 3)) θ)
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ)
          (qubitConfigFin (k + 3) j) (qubitConfigFin (k + 3) x))
        (zeroProductState (Fin (k + 3)))})
      ≤ ENNReal.ofReal (1 / L) := by
    refine le_trans (Measure.le_map_apply
      continuous_sphereCoeff.measurable.aemeasurable _) ?_
    rw [← shellProbability_eq_map_sphereLaw]
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr ?_
    rw [hc₀def]
    exact measureReal_spectralCollision_chainShell_ge_le (k + 2) hdisc hL
  have hGc : (sphereLaw (Fintype.card (ChainLabel (k + 3)))) Gᶜ ≤ ENNReal.ofReal (1 / L) := by
    have hsub : Gᶜ ⊆ (simpleLocus hP)ᶜ ∪
        sphereCoeff ⁻¹' {θ | c₀ ≤ spectralCollision
          (fun j x => hermitianEigenBasis (spectralEnsembleMatrix (chainPauliFin (k + 3)) θ)
            (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ)
            (qubitConfigFin (k + 3) j) (qubitConfigFin (k + 3) x))
          (zeroProductState (Fin (k + 3)))} := by
      intro x hx
      by_cases hxs : x ∈ simpleLocus hP
      · refine Or.inr ?_
        have hnot : ¬ (crossCollision hP Om x ≤ c₀) := by
          intro hlt
          exact hx (by rw [hGdef]; exact ⟨hxs, hlt⟩)
        show c₀ ≤ _
        have hcc : crossCollision hP Om x
            = spectralCollision
              (fun j y => hermitianEigenBasis
                (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
                (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3))
                  (sphereCoeff x))
                (qubitConfigFin (k + 3) j) (qubitConfigFin (k + 3) y))
              (zeroProductState (Fin (k + 3))) := by
          rw [crossCollision_eq hP Om hxs, hPdef, hOmdef]
          exact spectralCollision_sortedEigenBasis_chain (k + 3) (sphereCoeff x)
        rw [← hcc]
        exact le_of_lt (not_le.mp hnot)
      · exact Or.inl hxs
    calc (sphereLaw (Fintype.card (ChainLabel (k + 3)))) Gᶜ
        ≤ (sphereLaw (Fintype.card (ChainLabel (k + 3)))) ((simpleLocus hP)ᶜ ∪ _) :=
          measure_mono hsub
      _ ≤ (sphereLaw (Fintype.card (ChainLabel (k + 3)))) (simpleLocus hP)ᶜ
          + (sphereLaw (Fintype.card (ChainLabel (k + 3)))) _ := measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal (1 / L) := add_le_add (le_of_eq hSnull) hbad
      _ = ENNReal.ofReal (1 / L) := zero_add _
  have hRL : ∀ b : Fin (2 ^ (k + 3)) → ℝ, (∑ i, b i = 0) → b ≠ 0 →
      ∀ g : coeffSphere (Fintype.card (ChainLabel (k + 3))) → ℂ, Measurable g →
        ∀ Cb : ℝ, 0 ≤ Cb → (∀ x, ‖g x‖ ≤ Cb) →
        Tendsto (fun u : ℝ => ∫ x, g x *
            Complex.exp (-((u * sortedSpectralAction hP b (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ
              (Fin (Fintype.card (ChainLabel (k + 3)))))).toSphere)) (cocompact ℝ) (nhds 0) := by
    intro b hbsum hbne g hg Cb hC0 hC
    rw [hPdef]
    exact tendsto_integral_exp_sortedSpectralAction_zero_pauliChain k b hbsum hbne g hg hC0 hC
  have hmain := limsup_sphereLaw_capture_le hN hP hdisc hRL i₀ Om
    (by rw [hOmdef]; exact finiteComplexInner_chainInput (k + 3)) Z hZ ha hr
    (by rw [hc₀def]; exact hscale) hM hcard hs hGmeas hGsimple hGcoll hGc
  rw [hOmdef] at hmain
  exact hmain

/-- **`(18)`.**  The replica order prescribed by the card satisfies the replica scale condition. -/
theorem scale_of_replicaOrder {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (n : ℕ)
    {r : ℕ} (hrpos : 1 ≤ r) (hrle : (r : ℝ) ≤ a ^ 2 / (32 * L) * (3 / 2 : ℝ) ^ n) :
    16 * (L * (2 / 3 : ℝ) ^ n) / a ^ 2 ≤ 1 / (2 * r) := by
  have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hpow : (0 : ℝ) < (3 / 2 : ℝ) ^ n := by positivity
  have hkey : 16 * (L * (2 / 3 : ℝ) ^ n) / a ^ 2 = 1 / (2 * (a ^ 2 / (32 * L) * (3 / 2) ^ n)) := by
    have h23 : (2 / 3 : ℝ) ^ n = ((3 / 2 : ℝ) ^ n)⁻¹ := by
      rw [← inv_pow]
      norm_num
    rw [h23]
    field_simp
    ring
  rw [hkey]
  refine one_div_le_one_div_of_le (by positivity) ?_
  linarith [hrle]

/-- **`(21)`.**  Every sufficiently late common time has small easy-circuit shell mass. -/
theorem eventually_sphereLaw_chainCapture_le (k : ℕ)
    {C : Type*} [Fintype C] [Nonempty C]
    (i₀ : Fin (2 ^ (k + 3)))
    (Z : C → (Fin (2 ^ (k + 3)) → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {L : ℝ} (hL : 0 < L)
    (hscale : 16 * (L * (2 / 3 : ℝ) ^ (k + 3)) / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    {η : ENNReal} (hη : η ≠ 0) :
    ∀ᶠ t : ℝ in atTop, (sphereLaw (Fintype.card (ChainLabel (k + 3))))
        {x | ∃ κ : C, a ≤ finitePureStateFidelity
          (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
            (2 * Real.pi * t) *ᵥ chainInput (k + 3)) (Z κ)}
      < ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) + ENNReal.ofReal (1 / L) + η := by
  have hmain := limsup_sphereLaw_chainCapture_le k i₀ Z hZ ha hr hL hscale hM hcard hs
  have hfin : ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) + ENNReal.ofReal (1 / L) ≠ ⊤ := by
    simp [ENNReal.add_eq_top]
  refine Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hmain ?_)
  exact ENNReal.lt_add_right hfin hη

end

end GaloisForLFunctions.HTGeometry
