import GaloisForLFunctions.RHTower.DeningerArithmeticJetProductEquivalence

/-!
# Compact support of the continuous arithmetic dual

A continuous linear functional on a product of complex lines depends on finitely many coordinates.
Applying this elementary product-topology fact to the full Xi-jet reconstruction identifies every
continuous compact-support cohomology class with a finite linear combination of local Xi jets.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/--
A continuous complex-linear functional on a dependent product of complex lines has finite
coordinate support.
-/
theorem ContinuousLinearMap.exists_finite_pi_support
    {ι : Type*} {κ : ι → Type*}
    (L : ((i : ι) → κ i → ℂ) →L[ℂ] ℂ) :
    ∃ S : Finset ι,
      ∃ T : (i : ι) → Finset (κ i),
        ∀ a,
          L a =
            ∑ i : ↥S,
              ∑ k ∈ T i.1,
                a i.1 k *
                  L (Pi.single i.1 (Pi.single k 1)) := by
  have hball :
      Metric.ball (0 : ℂ) 1 ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hpre :
      L ⁻¹' Metric.ball (0 : ℂ) 1 ∈
        𝓝 (0 : (i : ι) → κ i → ℂ) := by
    have :=
      L.continuous.continuousAt.preimage_mem_nhds hball
    simpa only [map_zero] using this
  rw [nhds_pi, Filter.mem_pi,
    exists_finite_iff_finset] at hpre
  obtain ⟨S, V, hV, hVS⟩ := hpre
  have hinner :
      ∀ i, ∃ T : Finset (κ i),
        ∃ W : (k : κ i) → Set ℂ,
          (∀ k, W k ∈ 𝓝 (0 : ℂ)) ∧
            Set.pi (T : Set (κ i)) W ⊆ V i := by
    intro i
    have hi := hV i
    rw [nhds_pi, Filter.mem_pi,
      exists_finite_iff_finset] at hi
    exact hi
  let T : (i : ι) → Finset (κ i) :=
    fun i => Classical.choose (hinner i)
  let W : (i : ι) → (k : κ i) → Set ℂ :=
    fun i =>
      Classical.choose
        (Classical.choose_spec (hinner i))
  have hW :
      ∀ i k, W i k ∈ 𝓝 (0 : ℂ) :=
    fun i =>
      (Classical.choose_spec
        (Classical.choose_spec (hinner i))).1
  have hWV :
      ∀ i, Set.pi (T i : Set (κ i)) (W i) ⊆ V i :=
    fun i =>
      (Classical.choose_spec
        (Classical.choose_spec (hinner i))).2
  have hkernel :
      ∀ b : (i : ι) → κ i → ℂ,
        (∀ (i : ι), i ∈ S →
          ∀ k, k ∈ T i → b i k = 0) →
          L b = 0 := by
    intro b hb
    have hscaled :
        ∀ c : ℂ, c • b ∈
          L ⁻¹' Metric.ball (0 : ℂ) 1 := by
      intro c
      apply hVS
      intro i hi
      apply hWV i
      intro k hk
      have hzero : (c • b) i k = 0 := by
        simp [hb i hi k hk]
      rw [hzero]
      exact mem_of_mem_nhds (hW i k)
    by_contra hLb
    have hcontra :=
      hscaled (L b)⁻¹
    have hvalue :
        L ((L b)⁻¹ • b) = 1 := by
      rw [L.map_smul]
      simp [hLb]
    change
      L ((L b)⁻¹ • b) ∈
        Metric.ball (0 : ℂ) 1 at hcontra
    rw [hvalue] at hcontra
    simpa [Metric.mem_ball] using hcontra
  refine ⟨S, T, ?_⟩
  intro a
  let basisVector (i : ι) (k : κ i) :
      (j : ι) → κ j → ℂ :=
    Pi.single i (Pi.single k 1)
  let p : (i : ι) → κ i → ℂ :=
    ∑ i : ↥S,
      ∑ k ∈ T i.1,
        a i.1 k • basisVector i.1 k
  have hp :
      ∀ (i : ι), i ∈ S →
        ∀ k, k ∈ T i →
          p i k = a i k := by
    intro i hi k hk
    let iS : ↥S := ⟨i, hi⟩
    classical
    simp [p, basisVector, iS, hk]
  have hzero :
      L (a - p) = 0 := by
    apply hkernel
    intro i hi k hk
    simp [hp i hi k hk]
  have hLp :
      L a = L p := by
    have hsub := L.map_sub a p
    rw [hzero] at hsub
    exact sub_eq_zero.mp hsub.symm
  rw [hLp]
  simp only [p, basisVector, map_sum, L.map_smul,
    smul_eq_mul]

/-- Continuous-linear inverse of the all-jets reconstruction homeomorphism. -/
def deningerCompactOpenJetProductToH1 :
    DeningerArithmeticJetProduct →L[ℂ]
      DeningerArithmeticCompactOpenH1 where
  toFun := deningerCompactOpenH1JetHomeomorph.symm
  map_add' a b := by
    apply deningerCompactOpenH1AllJets_injective
    simp
  map_smul' c a := by
    apply deningerCompactOpenH1AllJets_injective
    simp
  cont :=
    deningerCompactOpenH1JetHomeomorph.symm.continuous

@[simp]
theorem deningerCompactOpenH1AllJets_jetProductToH1
    (a : DeningerArithmeticJetProduct) :
    deningerCompactOpenH1AllJets
        (deningerCompactOpenJetProductToH1 a) = a :=
  deningerCompactOpenH1JetHomeomorph.apply_symm_apply a

@[simp]
theorem deningerCompactOpenJetProductToH1_allJets
    (x : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenJetProductToH1
        (deningerCompactOpenH1AllJets x) = x :=
  deningerCompactOpenH1JetHomeomorph.symm_apply_apply x

/--
Every continuous compact-support class is a finite linear combination of local Xi-jet
functionals.
-/
theorem deningerArithmeticTopologicalH1Compact_finiteJetSupport
    (ell : DeningerArithmeticTopologicalH1Compact) :
    ∃ S : Finset XiDivisorSupport,
      ∃ T :
          (rho : XiDivisorSupport) →
            Finset (DeningerArithmeticJetIndex rho),
        ∀ x,
          ell x =
            ∑ rho : ↥S,
              ∑ k ∈ T rho.1,
                deningerCompactOpenH1Jet rho.1 k x *
                  ell
                    (deningerCompactOpenJetProductToH1
                      (Pi.single rho.1
                        (Pi.single k 1))) := by
  let L :
      DeningerArithmeticJetProduct →L[ℂ] ℂ :=
    ell.comp deningerCompactOpenJetProductToH1
  obtain ⟨S, T, hL⟩ :=
    L.exists_finite_pi_support
  refine ⟨S, T, fun x => ?_⟩
  have hformula :=
    hL (deningerCompactOpenH1AllJets x)
  change
    ell x =
      ∑ rho : ↥S,
        ∑ k ∈ T rho.1,
          deningerCompactOpenH1Jet rho.1 k x *
            ell
              (deningerCompactOpenJetProductToH1
                (Pi.single rho.1
                  (Pi.single k 1)))
  simpa only [L, ContinuousLinearMap.comp_apply,
    deningerCompactOpenJetProductToH1_allJets,
    deningerCompactOpenH1AllJets_apply] using hformula

end

end RHTower
