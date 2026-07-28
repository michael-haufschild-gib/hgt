import GaloisForLFunctions.RHTower.LocalHamiltonianCausalHorizonLaw

/-!
# Optimal local-future energy law

The complete local future interval is achievable with Hamiltonian norm
growing at most linearly in the hidden radius.  Together with the converse
in `LocalHamiltonianCausalHorizonLaw`, this makes linear
energy-times-time versus distance scaling necessary and sufficient up to
universal constants.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower.ParityForecast

/-- One exponent, depending only on the fixed observation window and
tolerance, works for every requested moment order.  The resulting odd
spectral index grows at most linearly in that order. -/
theorem exists_uniformWindowExponent_endpointN_record
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℕ, ∀ m : ℕ,
      ∃ q : ℕ,
        q ≤ m + a ∧
        m < endpointN q ∧
        ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
          (∀ k : ℕ, k ≤ m →
            ∑ j : Fin (endpointN q + 1),
                interpolatedWeight (endpointN q) (Real.sqrt p) j *
                  scaledEnergy T (endpointN q) j ^ k =
              ∑ j : Fin (endpointN q + 1),
                fullWeight (endpointN q) j *
                  scaledEnergy T (endpointN q) j ^ k) ∧
          (∀ t : ℝ, |t| ≤ H →
            |scaledInterpolatedProbability
                T (endpointN q) (Real.sqrt p) t -
              scaledFullProbability T (endpointN q) t| < δ) ∧
          scaledInterpolatedProbability
              T (endpointN q) (Real.sqrt p) T = p := by
  let ρ := H / T
  have hρ0 : 0 ≤ ρ := div_nonneg hH0 hT.le
  have hρ1 : ρ < 1 := (div_lt_one hT).2 hHT
  let s := Real.sin (Real.pi * ρ / 2)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hs1 : s < 1 := by
    dsimp [s]
    rw [← Real.sin_pi_div_two]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · exact le_rfl
    · nlinarith [Real.pi_pos]
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hhalf hs1
  refine ⟨a, ?_⟩
  intro m
  let q := max m a
  have hmq : m ≤ q := le_max_left _ _
  have haq : a ≤ q := le_max_right _ _
  have hqbound : q ≤ m + a := by
    dsimp [q]
    omega
  have hmn : m < endpointN q := by
    simp [endpointN]
    omega
  have han : a ≤ endpointN q := by
    simp [endpointN]
    omega
  have hn : 0 < endpointN q := by simp [endpointN]
  refine ⟨q, hqbound, hmn, ?_⟩
  intro p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact scaled_interpolated_energyMoment_eq
      (lt_of_le_of_lt hk hmn) _
  · intro t ht
    let τ := t / T
    have hτ : |τ| ≤ ρ := by
      dsimp [τ, ρ]
      rw [abs_div, abs_of_pos hT]
      exact (div_le_div_iff_of_pos_right hT).2 ht
    have hwindow :=
      amplitude_difference_window_bound (endpointN q) hρ1.le hτ
    have hpow : s ^ endpointN q ≤ s ^ a :=
      pow_le_pow_of_le_one hs0 hs1.le han
    have hparity :
        ‖parityAmplitude (endpointN q) τ -
          fullAmplitude (endpointN q) τ‖ < δ / 2 :=
      lt_of_le_of_lt
        (hwindow.trans (by simpa [s, ρ] using hpow)) ha
    have hamp :
        ‖interpolatedAmplitude
            (endpointN q) (Real.sqrt p) τ -
          fullAmplitude (endpointN q) τ‖ < δ / 2 := by
      rw [interpolatedAmplitude_difference_norm
        (endpointN q) hθ0]
      have hmul :
          Real.sqrt p *
              ‖parityAmplitude (endpointN q) τ -
                fullAmplitude (endpointN q) τ‖ ≤
            ‖parityAmplitude (endpointN q) τ -
              fullAmplitude (endpointN q) τ‖ := by
        nlinarith
          [norm_nonneg
            (parityAmplitude (endpointN q) τ -
              fullAmplitude (endpointN q) τ)]
      exact lt_of_le_of_lt hmul hparity
    change
      |interpolatedProbability
          (endpointN q) (Real.sqrt p) τ -
        fullProbability (endpointN q) τ| < δ
    exact lt_of_le_of_lt
      (interpolated_probability_difference_le_amplitude
        hn hθ0 hθ1 τ) (by linarith)
  · rw [scaledInterpolatedProbability_target
      hT hn hθ0, Real.sq_sqrt hp.1]

theorem FixedEndpointPathModel.norm_le
    {T : ℝ} (hT : 0 < T) {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) :
    ‖M.hamiltonian‖ ≤ Real.pi * n / T :=
  fixedProtocolHamiltonian_norm_le hT n M.unitary

/-- A unitary coordinate change as a unit in the Banach algebra of bounded
endomorphisms. -/
def linearIsometryEquivUnit
    {n : ℕ} (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    (ClockSpace n →L[ℂ] ClockSpace n)ˣ :=
  { val := U
    inv := U.symm
    val_inv := by
      ext x
      simp
    inv_val := by
      ext x
      simp }

set_option synthInstance.maxHeartbeats 200000 in
/-- Exponentiating a finite diagonal Hamiltonian acts coordinatewise by the
ordinary complex exponential. -/
theorem finiteIndexDiagonal_exp_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) (c : ℂ)
    (x : FiniteIndexClockSpace ι) (i : ι) :
    (NormedSpace.exp
        (c • finiteIndexDiagonalHamiltonian energy)) x i =
      Complex.exp (c * energy i) * x i := by
  let φ :
      (FiniteIndexClockSpace ι →L[ℂ] FiniteIndexClockSpace ι) →L[ℂ] ℂ :=
    (EuclideanSpace.proj i).comp
      ((ContinuousLinearMap.apply ℂ (FiniteIndexClockSpace ι)) x)
  have hop :=
    (NormedSpace.exp_series_hasSum_exp'
      (𝕂 := ℂ) (c • finiteIndexDiagonalHamiltonian energy)).map
        φ φ.continuous
  have hscalar :=
    NormedSpace.exp_series_hasSum_exp'
      (𝕂 := ℂ) (c * (energy i : ℂ))
  have hscalar' :
      HasSum
        (fun m : ℕ =>
          ((m.factorial : ℂ)⁻¹ * (c * (energy i : ℂ)) ^ m) *
            x i)
        (Complex.exp (c * energy i) * x i) := by
    simpa only [Complex.exp_eq_exp_ℂ] using hscalar.mul_right (x i)
  have hop' :
      HasSum
        (fun m : ℕ =>
          ((m.factorial : ℂ)⁻¹ * (c * (energy i : ℂ)) ^ m) *
            x i)
        ((NormedSpace.exp
          (c • finiteIndexDiagonalHamiltonian energy)) x i) := by
    convert hop using 1
    funext m
    unfold φ
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, EuclideanSpace.coe_proj,
      ContinuousLinearMap.smul_apply, smul_pow,
      PiLp.smul_apply, smul_eq_mul]
    rw [mul_pow]
    rw [finiteIndexDiagonalHamiltonian_pow_apply]
    ring
  exact hop'.unique hscalar'

/-- The explicit spectral trajectory is the literal exponential orbit of
the shared diagonal Hamiltonian. -/
theorem scaledClock_exp_interpolatedClock
    (T : ℝ) (n : ℕ) (θ t : ℝ) :
    (NormedSpace.exp
        (((t : ℂ) * Complex.I) • scaledClockHamiltonian T n))
        (interpolatedClock n θ) =
      scaledInterpolatedClockAt T n θ t := by
  ext j
  rw [scaledClockHamiltonian,
    finiteIndexDiagonal_exp_apply]
  simp only [interpolatedClock, finiteIndexWeightKet_apply,
    scaledInterpolatedClockAt, finiteIndexPhasedWeightKet_apply,
    scaledPhase_eq_angular]
  rw [show
      Complex.exp
          (((t : ℂ) * Complex.I) *
            (angularEnergy T n j : ℂ)) =
        Complex.exp
          (((angularEnergy T n j * t : ℝ) : ℂ) *
            Complex.I) by
      congr 1
      push_cast
      ring]
  ring

set_option synthInstance.maxHeartbeats 100000 in
/-- Operator exponentiation commutes exactly with the fixed-protocol
unitary change of coordinates. -/
theorem fixedProtocol_exp_apply
    (T : ℝ) (n : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n)
    (c : ℂ) (x : ClockSpace n) :
    (NormedSpace.exp
        (c • fixedProtocolHamiltonian T n U)) x =
      U.symm
        ((NormedSpace.exp (c • scaledClockHamiltonian T n))
          (U x)) := by
  letI : NormedAlgebra ℚ
      (ClockSpace n →L[ℂ] ClockSpace n) :=
    .restrictScalars ℚ ℂ (ClockSpace n →L[ℂ] ClockSpace n)
  let u := linearIsometryEquivUnit U
  have harg :
      c • fixedProtocolHamiltonian T n U =
        (↑u⁻¹ : ClockSpace n →L[ℂ] ClockSpace n) *
          (c • scaledClockHamiltonian T n) *
          (↑u : ClockSpace n →L[ℂ] ClockSpace n) := by
    ext y
    simp [u, linearIsometryEquivUnit, fixedProtocolHamiltonian]
  rw [harg, NormedSpace.exp_units_conj']
  simp [u, linearIsometryEquivUnit]

/-- Every constructed fixed-endpoint state is exactly its Hamiltonian's
standard unitary exponential evolution. -/
theorem FixedEndpointPathModel.stateAt_eq_exp
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (t : ℝ) :
    M.stateAt t =
      (NormedSpace.exp
        (((t : ℂ) * Complex.I) • M.hamiltonian))
        (fixedClock n) := by
  change M.stateAt t =
    (NormedSpace.exp
      (((t : ℂ) * Complex.I) •
        fixedProtocolHamiltonian T n M.unitary))
      (fixedClock n)
  rw [fixedProtocol_exp_apply]
  unfold FixedEndpointPathModel.stateAt
  rw [M.prepares]
  simp only [map_smul]
  rw [scaledClock_exp_interpolatedClock]

/-- The construction's declared return probability is literally the
operator-exponential return probability used by the causal converse. -/
theorem FixedEndpointPathModel.returnProbability_eq_exponential
    {T : ℝ} {n : ℕ} {θ : ℝ}
    (M : FixedEndpointPathModel T n θ) (t : ℝ) :
    M.returnProbability t =
      endpointExponentialReturnProbability M.hamiltonian t := by
  unfold FixedEndpointPathModel.returnProbability
  unfold endpointExponentialReturnProbability
  rw [endpointExponentialAmplitude_eq_inner_exp,
    ← M.stateAt_eq_exp, Complex.normSq_eq_norm_sq]

/-- Compatible future set with an explicit common gauge-centered Hamiltonian
norm ceiling.  The center is the midpoint of the shared spectrum. -/
def energyBoundedLocalCompatibleFutureSet
    (R : ℕ) (T H δ E : ℝ) (q : ℕ)
    (baseline : FixedEndpointPathModel T (endpointN q) 0) :
    Set ℝ :=
  {p | ∃ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ M : FixedEndpointPathModel T (endpointN q) θ,
      NearestNeighborHamiltonian M.hamiltonian ∧
      ContinuousLinearMap.adjoint M.hamiltonian = M.hamiltonian ∧
      (∀ x : ClockSpace (endpointN q),
        M.unitary (M.hamiltonian x) =
          scaledClockHamiltonian T (endpointN q) (M.unitary x)) ∧
      EndpointLocalMatrixEq R M.hamiltonian baseline.hamiltonian ∧
      (∀ t : ℝ, |t| ≤ H →
        |M.returnProbability t -
          baseline.returnProbability t| < δ) ∧
      M.returnProbability T = p ∧
      ‖energyGaugeShift (clockEnergyCenter T (endpointN q))
          M.hamiltonian‖ ≤ E}

/--
**Linear achievability of complete local futures.**

For fixed target time, observation window and tolerance, one constant `a`
works for every local radius `R`.  At that radius there is one finite
isospectral nearest-neighbour record whose norm-bounded compatible future set
is exactly `[0,1]`, with common norm ceiling

`π (4R + 2a + 5) / (2T)`.

Hence the energy-times-time cost of retaining every possible future is at
most linear in hidden distance.
-/
theorem exists_linearEnergy_completeLocalFutureSet
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℕ, ∀ R : ℕ,
      ∃ q : ℕ,
        q ≤ 2 * R + 2 + a ∧
        endpointN q ≤ 4 * R + 2 * a + 5 ∧
        ∃ baseline : FixedEndpointPathModel T (endpointN q) 0,
          NearestNeighborHamiltonian baseline.hamiltonian ∧
          ContinuousLinearMap.adjoint baseline.hamiltonian =
            baseline.hamiltonian ∧
          ‖energyGaugeShift
              (clockEnergyCenter T (endpointN q))
              baseline.hamiltonian‖ ≤
            Real.pi * ((4 * R + 2 * a + 5 : ℕ) : ℝ) / (2 * T) ∧
          energyBoundedLocalCompatibleFutureSet
              R T H δ
              (Real.pi * ((4 * R + 2 * a + 5 : ℕ) : ℝ) / (2 * T))
              q baseline =
            Set.Icc (0 : ℝ) 1 := by
  obtain ⟨a, ha⟩ :=
    exists_uniformWindowExponent_endpointN_record
      T H hT hH0 hHT hδ
  refine ⟨a, ?_⟩
  intro R
  obtain ⟨q, hqbound, horder, hall⟩ := ha (2 * R + 2)
  have hdim : endpointN q ≤ 4 * R + 2 * a + 5 := by
    simp [endpointN] at *
    omega
  have hn : 0 < endpointN q := by simp [endpointN]
  have hsize : R + 2 ≤ endpointN q + 1 := by omega
  obtain ⟨c₀, hc₀, hzero₀, _hprob₀⟩ :=
    exists_canonicalInterpolatedPathPhase
      hT hn (θ := 0) (by norm_num) (by norm_num)
  let baseline :
      FixedEndpointPathModel T (endpointN q) 0 :=
    { unitary :=
        canonicalKrylovUnitary
          (angularEnergy T (endpointN q))
          (interpolatedWeight (endpointN q) 0)
          (angularEnergy_injective hT (endpointN q))
          (interpolatedWeight_pos (endpointN q)
            (by norm_num) (by norm_num))
      phase := c₀
      phase_norm := hc₀
      prepares := hzero₀ }
  have hbaselineHamiltonian :
      baseline.hamiltonian =
        canonicalKrylovPathHamiltonian
          (angularEnergy T (endpointN q))
          (interpolatedWeight (endpointN q) 0)
          (angularEnergy_injective hT (endpointN q))
          (interpolatedWeight_pos (endpointN q)
            (by norm_num) (by norm_num)) := by
    exact (canonicalKrylovPathHamiltonian_eq_fixedProtocol
      hT (endpointN q) (θ := 0)
      (by norm_num) (by norm_num)).symm
  have hbaselineNN :
      NearestNeighborHamiltonian baseline.hamiltonian := by
    rw [hbaselineHamiltonian]
    exact canonicalKrylovPathHamiltonian_nearestNeighbor
      (angularEnergy_injective hT (endpointN q))
      (interpolatedWeight_pos (endpointN q)
        (by norm_num) (by norm_num))
  let E : ℝ :=
    Real.pi * ((4 * R + 2 * a + 5 : ℕ) : ℝ) / (2 * T)
  have hnormTransfer :
      clockEnergyCenter T (endpointN q) ≤ E := by
    unfold clockEnergyCenter
    dsimp [E]
    gcongr
  have hbaselineNorm :
      ‖energyGaugeShift (clockEnergyCenter T (endpointN q))
          baseline.hamiltonian‖ ≤ E :=
    (fixedProtocolHamiltonian_centered_norm_le
      hT (endpointN q) baseline.unitary).trans hnormTransfer
  have hrealize :
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        ∃ M :
            FixedEndpointPathModel
              T (endpointN q) (Real.sqrt p),
          NearestNeighborHamiltonian M.hamiltonian ∧
          ContinuousLinearMap.adjoint M.hamiltonian =
            M.hamiltonian ∧
          (∀ x : ClockSpace (endpointN q),
            M.unitary (M.hamiltonian x) =
              scaledClockHamiltonian T (endpointN q)
                (M.unitary x)) ∧
          EndpointLocalMatrixEq
            R M.hamiltonian baseline.hamiltonian ∧
          (∀ t : ℝ, |t| ≤ H →
            |M.returnProbability t -
              baseline.returnProbability t| < δ) ∧
          M.returnProbability T = p ∧
          ‖energyGaugeShift (clockEnergyCenter T (endpointN q))
              M.hamiltonian‖ ≤ E := by
    intro p hp
    obtain ⟨_hmoment, hwindow, htarget⟩ := hall p hp
    have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
    have hθle : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
    by_cases hp1 : p = 1
    · subst p
      obtain ⟨c, hc, hzero, _hprob⟩ :=
        exists_endpointCanonicalPathPhase hT q
      let M :
          FixedEndpointPathModel
            T (endpointN q) (Real.sqrt 1) :=
        { unitary := endpointCanonicalKrylovUnitary hT q
          phase := c
          phase_norm := hc
          prepares := by
            simpa [interpolatedClock_one] using hzero }
      have hMHamiltonian :
          M.hamiltonian = endpointCanonicalPathHamiltonian hT q := by
        rfl
      have hRq : R + 2 ≤ q + 1 := by
        simp [endpointN] at horder
        omega
      have hMNN : NearestNeighborHamiltonian M.hamiltonian := by
        rw [hMHamiltonian]
        exact endpointCanonicalPathHamiltonian_nearestNeighbor hT q
      have hprefix :
          ∀ i j : Fin (R + 2),
            (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
            inner ℂ
                (EuclideanSpace.basisFun
                  (Fin (endpointN q + 1)) ℂ
                  (Fin.castLE hsize i))
                (M.hamiltonian
                  (EuclideanSpace.basisFun
                    (Fin (endpointN q + 1)) ℂ
                    (Fin.castLE hsize j))) =
              inner ℂ
                (EuclideanSpace.basisFun
                  (Fin (endpointN q + 1)) ℂ
                  (Fin.castLE hsize i))
                (baseline.hamiltonian
                  (EuclideanSpace.basisFun
                    (Fin (endpointN q + 1)) ℂ
                    (Fin.castLE hsize j))) := by
        intro i j hdegree
        rw [hMHamiltonian, hbaselineHamiltonian]
        exact endpointCanonicalPathHamiltonian_local_eq_full
          R hT q hRq i j hdegree
      refine ⟨M, hMNN, M.selfAdjoint, M.intertwines,
        endpointLocalMatrixEq_of_prefix
          hsize hMNN hbaselineNN hprefix, ?_, ?_, ?_⟩
      · intro t ht
        rw [M.returnProbability_eq hT
            (Real.sqrt_nonneg 1) (Real.sqrt_le_one.mpr (by norm_num)),
          baseline.returnProbability_eq hT (by norm_num) (by norm_num)]
        simpa [scaledInterpolatedProbability,
          interpolatedProbability, interpolatedAmplitude,
          interpolatedWeight] using hwindow t ht
      · rw [M.returnProbability_eq hT
          (Real.sqrt_nonneg 1) (Real.sqrt_le_one.mpr (by norm_num))]
        exact htarget
      · exact (fixedProtocolHamiltonian_centered_norm_le
          hT (endpointN q) M.unitary).trans hnormTransfer
    · have hp_lt : p < 1 := lt_of_le_of_ne hp.2 hp1
      have hθlt : Real.sqrt p < 1 := by
        rw [Real.sqrt_lt' zero_lt_one]
        simpa using hp_lt
      obtain ⟨c, hc, hzero, _hprob⟩ :=
        exists_canonicalInterpolatedPathPhase hT hn hθ0 hθlt
      let M :
          FixedEndpointPathModel
            T (endpointN q) (Real.sqrt p) :=
        { unitary :=
            canonicalKrylovUnitary
              (angularEnergy T (endpointN q))
              (interpolatedWeight (endpointN q) (Real.sqrt p))
              (angularEnergy_injective hT (endpointN q))
              (interpolatedWeight_pos (endpointN q) hθ0 hθlt)
          phase := c
          phase_norm := hc
          prepares := hzero }
      have hMHamiltonian :
          M.hamiltonian =
            canonicalKrylovPathHamiltonian
              (angularEnergy T (endpointN q))
              (interpolatedWeight (endpointN q) (Real.sqrt p))
              (angularEnergy_injective hT (endpointN q))
              (interpolatedWeight_pos (endpointN q)
                hθ0 hθlt) := by
        exact (canonicalKrylovPathHamiltonian_eq_fixedProtocol
          hT (endpointN q) hθ0 hθlt).symm
      have hMNN : NearestNeighborHamiltonian M.hamiltonian := by
        rw [hMHamiltonian]
        exact canonicalKrylovPathHamiltonian_nearestNeighbor
          (angularEnergy_injective hT (endpointN q))
          (interpolatedWeight_pos (endpointN q) hθ0 hθlt)
      have hprefix :
          ∀ i j : Fin (R + 2),
            (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
            inner ℂ
                (EuclideanSpace.basisFun
                  (Fin (endpointN q + 1)) ℂ
                  (Fin.castLE hsize i))
                (M.hamiltonian
                  (EuclideanSpace.basisFun
                    (Fin (endpointN q + 1)) ℂ
                    (Fin.castLE hsize j))) =
              inner ℂ
                (EuclideanSpace.basisFun
                  (Fin (endpointN q + 1)) ℂ
                  (Fin.castLE hsize i))
                (baseline.hamiltonian
                  (EuclideanSpace.basisFun
                    (Fin (endpointN q + 1)) ℂ
                    (Fin.castLE hsize j))) := by
        intro i j hdegree
        rw [hMHamiltonian, hbaselineHamiltonian]
        apply canonicalKrylovPathHamiltonian_local_eq_of_moments_of_size
          (R := R) (r := endpointN q + 1) hsize
          (angularEnergy T (endpointN q))
          (interpolatedWeight (endpointN q) (Real.sqrt p))
          (interpolatedWeight (endpointN q) 0)
          (angularEnergy_injective hT (endpointN q))
          (interpolatedWeight_pos (endpointN q) hθ0 hθlt)
          (interpolatedWeight_pos (endpointN q)
            (by norm_num) (by norm_num))
          ?_ i j hdegree
        intro d hd
        calc
          (∑ x : Fin (endpointN q + 1),
              interpolatedWeight (endpointN q) (Real.sqrt p) x *
                angularEnergy T (endpointN q) x ^ d) =
            ∑ x : Fin (endpointN q + 1),
              fullWeight (endpointN q) x *
                angularEnergy T (endpointN q) x ^ d :=
              angular_interpolated_energyMoment_eq_full
                (by omega) (Real.sqrt p)
          _ = ∑ x : Fin (endpointN q + 1),
              interpolatedWeight (endpointN q) 0 x *
                angularEnergy T (endpointN q) x ^ d :=
            (angular_interpolated_energyMoment_eq_full
              (by omega) 0).symm
      refine ⟨M, hMNN, M.selfAdjoint, M.intertwines,
        endpointLocalMatrixEq_of_prefix
          hsize hMNN hbaselineNN hprefix, ?_, ?_, ?_⟩
      · intro t ht
        rw [M.returnProbability_eq hT hθ0 hθle,
          baseline.returnProbability_eq hT (by norm_num) (by norm_num)]
        simpa [scaledInterpolatedProbability,
          interpolatedProbability, interpolatedAmplitude,
          interpolatedWeight] using hwindow t ht
      · rw [M.returnProbability_eq hT hθ0 hθle]
        exact htarget
      · exact (fixedProtocolHamiltonian_centered_norm_le
          hT (endpointN q) M.unitary).trans hnormTransfer
  refine ⟨q, hqbound, hdim, baseline, hbaselineNN,
    baseline.selfAdjoint, hbaselineNorm, ?_⟩
  ext p
  constructor
  · intro hp
    rcases hp with
      ⟨θ, hθ, M, _hMNN, _hMSA, _hintertwines,
        _hlocal, _hwindow, htarget, _hMnorm⟩
    have hpEq : p = θ ^ 2 := by
      rw [← htarget, M.returnProbability_eq hT hθ.1 hθ.2,
        scaledInterpolatedProbability_target hT hn hθ.1]
    constructor
    · rw [hpEq]
      positivity
    · rw [hpEq]
      nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2)]
  · intro hp
    obtain ⟨M, hMNN, hMSA, hintertwines,
        hlocal, hwindow, htarget, hMnorm⟩ := hrealize p hp
    exact ⟨Real.sqrt p,
      ⟨Real.sqrt_nonneg p, Real.sqrt_le_one.mpr hp.2⟩,
      M, hMNN, hMSA, hintertwines, hlocal, hwindow,
      htarget, hMnorm⟩

end RHTower.ParityForecast
