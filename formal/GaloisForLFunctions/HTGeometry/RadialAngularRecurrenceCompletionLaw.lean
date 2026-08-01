import GaloisForLFunctions.HTGeometry.FiniteHorizonTemporalDimensionIndistinguishabilityLaw

/-!
# Radial--angular completion law for recurrence

Finite observations do not determine which spectral modes persist at late
time.  A uniform radial damping of any unitary carrier is invisible on every
prescribed finite horizon, for every operator-normalized observable, yet its
complete Heisenberg history vanishes.  Independently, arbitrarily small
angular perturbations realize every positive completed temporal rank.

The two operations act on one reference unitary dynamics.  Radial damping
chooses whether any carrier survives; angular arithmetic chooses the
dimension of recurrence when it does.
-/

open Filter
open NormedSpace
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Uniform radial damping of a bounded history. -/
def uniformlyDampedHistory
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (u : ℕ → E) (n : ℕ) : E :=
  (r ^ n) • u n

/-- Bernoulli's inequality gives a dimension-free finite-horizon bound for
uniform radial damping. -/
theorem norm_uniformlyDampedHistory_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    ‖uniformlyDampedHistory r u n - u n‖ ≤
      (n : ℝ) * (1 - r) := by
  have hrpow0 : 0 ≤ r ^ n := pow_nonneg hr0 n
  have hrpow1 : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1
  have hbern : 1 + (n : ℝ) * (r - 1) ≤ r ^ n :=
    one_add_mul_sub_le_pow (by linarith) n
  have hgap : 1 - r ^ n ≤ (n : ℝ) * (1 - r) := by
    linarith
  calc
    ‖uniformlyDampedHistory r u n - u n‖ =
        ‖(r ^ n - 1) • u n‖ := by
          rw [uniformlyDampedHistory, sub_smul, one_smul]
    _ = |r ^ n - 1| * ‖u n‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = (1 - r ^ n) * ‖u n‖ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hrpow1)]
      ring
    _ ≤ (1 - r ^ n) * 1 := by
      exact mul_le_mul_of_nonneg_left (hu n) (sub_nonneg.mpr hrpow1)
    _ ≤ (n : ℝ) * (1 - r) := by simpa using hgap

/-- Every uniformly bounded history vanishes after any fixed strict radial
damping. -/
theorem uniformlyDampedHistory_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (uniformlyDampedHistory r u) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  rw [uniformlyDampedHistory, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hr0 _)]
  exact mul_le_of_le_one_right (pow_nonneg hr0 _) (hu n)

/-- Every finite prefix of a uniformly bounded history is compatible, to
arbitrary positive tolerance, with a complete history that vanishes. -/
theorem exists_uniformlyDampedHistory_finiteHorizon_close_extinct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ n ≤ N, ‖uniformlyDampedHistory r u n - u n‖ < η) ∧
      Tendsto (uniformlyDampedHistory r u) atTop (𝓝 0) := by
  let δ : ℝ := min (1 / 2 : ℝ) (η / (2 * ((N : ℝ) + 1)))
  let r : ℝ := 1 - δ
  have hN1 : 0 < (N : ℝ) + 1 := by positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hη (mul_pos (by norm_num) hN1))
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδeta : δ ≤ η / (2 * ((N : ℝ) + 1)) := min_le_right _ _
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hrlt : r < 1 := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := hrpos.le
  have hr1 : r ≤ 1 := hrlt.le
  refine ⟨r, hrpos, hrlt, ?_,
    uniformlyDampedHistory_tendsto_zero u hu hr0 hrlt⟩
  intro n hn
  have hncast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hbound := norm_uniformlyDampedHistory_sub_le u hu hr0 hr1 n
  have hmul : (n : ℝ) * (1 - r) ≤
      (N : ℝ) * (η / (2 * ((N : ℝ) + 1))) := by
    have hgap : 1 - r = δ := by simp [r]
    rw [hgap]
    calc
      (n : ℝ) * δ ≤ (N : ℝ) * δ := by gcongr
      _ ≤ (N : ℝ) * (η / (2 * ((N : ℝ) + 1))) := by gcongr
  have hlast : (N : ℝ) * (η / (2 * ((N : ℝ) + 1))) < η := by
    rw [div_eq_mul_inv]
    have hden : 0 < 2 * ((N : ℝ) + 1) := by positivity
    have hratio : (N : ℝ) * (2 * ((N : ℝ) + 1))⁻¹ < 1 := by
      rw [← div_eq_mul_inv, div_lt_one hden]
      nlinarith
    calc
      (N : ℝ) * (η * (2 * ((N : ℝ) + 1))⁻¹) =
          η * ((N : ℝ) * (2 * ((N : ℝ) + 1))⁻¹) := by ring
      _ < η * 1 := mul_lt_mul_of_pos_left hratio hη
      _ = η := mul_one η
  exact hbound.trans_lt (hmul.trans_lt hlast)

variable {A : Type*} [CStarAlgebra A]

/-- Two contractive conjugations are Lipschitz in their carriers. -/
theorem contraction_conjugation_norm_sub_le
    (U V O : A) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖U * O * star U - V * O * star V‖ ≤
      2 * ‖U - V‖ * ‖O‖ := by
  have hsplit :
      U * O * star U - V * O * star V =
        (U - V) * O * star U + V * O * (star U - star V) := by
    noncomm_ring
  rw [hsplit]
  calc
    ‖(U - V) * O * star U + V * O * (star U - star V)‖
        ≤ ‖(U - V) * O * star U‖ +
          ‖V * O * (star U - star V)‖ := norm_add_le _ _
    _ ≤ (‖U - V‖ * ‖O‖) * ‖star U‖ +
          (‖V‖ * ‖O‖) * ‖star U - star V‖ := by
      exact add_le_add
        ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ = (‖U - V‖ * ‖O‖) * ‖U‖ +
          (‖V‖ * ‖O‖) * ‖U - V‖ := by
      rw [norm_star, ← star_sub, norm_star]
    _ ≤ (‖U - V‖ * ‖O‖) * 1 +
          (1 * ‖O‖) * ‖U - V‖ := by gcongr
    _ = 2 * ‖U - V‖ * ‖O‖ := by ring

/-- A strict contraction can reproduce every finite prefix of a unitary
carrier arbitrarily well while its complete carrier vanishes. -/
theorem exists_scalarDampedUnitary_finiteHorizon_close_extinct
    [Nontrivial A] (U : A) (hU : U ∈ unitary A)
    (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ‖(r : ℂ) • U‖ < 1 ∧
      (∀ n ≤ N, ‖(((r : ℂ) • U) ^ n) - U ^ n‖ < η) ∧
      Tendsto (fun n => (((r : ℂ) • U) ^ n)) atTop (𝓝 0) := by
  let u : ℕ → A := fun n => U ^ n
  have hu : ∀ n, ‖u n‖ ≤ 1 := by
    intro n
    rw [show ‖u n‖ = 1 by
      exact CStarRing.norm_of_mem_unitary ((unitary A).pow_mem hU n)]
  obtain ⟨r, hr0, hr1, hclose, _⟩ :=
    exists_uniformlyDampedHistory_finiteHorizon_close_extinct
      u hu N η hη
  have hnormr : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hdamped : ‖(r : ℂ) • U‖ < 1 := by
    rw [norm_smul, hnormr, CStarRing.norm_of_mem_unitary hU, mul_one]
    exact hr1
  refine ⟨r, hr0, hr1, hdamped, ?_, ?_⟩
  · intro n hn
    simpa [uniformlyDampedHistory, u, smul_pow, Complex.real_smul] using
      hclose n hn
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
    rw [smul_pow, norm_smul, norm_pow, hnormr,
      CStarRing.norm_of_mem_unitary ((unitary A).pow_mem hU n), mul_one]

/-- The same finite normalized-observable record is compatible with a
unitary carrier and with an asymptotically extinct strict contraction. -/
theorem exists_scalarDampedUnitary_heisenberg_finiteHorizon_close_extinct
    [Nontrivial A] (U : A) (hU : U ∈ unitary A)
    (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ‖(r : ℂ) • U‖ < 1 ∧
      (∀ n ≤ N, ∀ O : A, ‖O‖ ≤ 1 →
        ‖(((r : ℂ) • U) ^ n) * O * star (((r : ℂ) • U) ^ n) -
          (U ^ n) * O * star (U ^ n)‖ < η) ∧
      ∀ O : A,
        Tendsto
          (fun n => (((r : ℂ) • U) ^ n) * O *
            star (((r : ℂ) • U) ^ n)) atTop (𝓝 0) := by
  obtain ⟨r, hr0, hr1, hdamped, hclose, hzero⟩ :=
    exists_scalarDampedUnitary_finiteHorizon_close_extinct
      U hU N (η / 2) (by positivity)
  refine ⟨r, hr0, hr1, hdamped, ?_, ?_⟩
  · intro n hn O hO
    have hUn : ‖U ^ n‖ ≤ 1 := by
      rw [CStarRing.norm_of_mem_unitary ((unitary A).pow_mem hU n)]
    have hVn : ‖((r : ℂ) • U) ^ n‖ ≤ 1 := by
      calc
        ‖((r : ℂ) • U) ^ n‖ ≤ ‖(r : ℂ) • U‖ ^ n := norm_pow_le _ _
        _ ≤ 1 ^ n := by gcongr
        _ = 1 := by simp
    have hbound := contraction_conjugation_norm_sub_le
      (((r : ℂ) • U) ^ n) (U ^ n) O hVn hUn
    have hdist := hclose n hn
    have hnormFactor :
        2 * ‖((r : ℂ) • U) ^ n - U ^ n‖ * ‖O‖ ≤
          2 * ‖((r : ℂ) • U) ^ n - U ^ n‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hO
        (mul_nonneg (by norm_num) (norm_nonneg _))
    calc
      _ ≤ 2 * ‖((r : ℂ) • U) ^ n - U ^ n‖ * ‖O‖ := hbound
      _ ≤ 2 * ‖((r : ℂ) • U) ^ n - U ^ n‖ * 1 := hnormFactor
      _ < η := by nlinarith
  · intro O
    simpa using (hzero.mul_const O).mul hzero.star

/-- One-step unitary generated by a finite diagonal Hamiltonian. -/
def finiteIndexUnitaryEvolution
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
      RHTower.FiniteIndexClockSpace (Fin (d + 1)) :=
  exp ((-Complex.I) • RHTower.finiteIndexDiagonalHamiltonian energy)

/-- The one-step finite diagonal evolution is unitary. -/
theorem finiteIndexUnitaryEvolution_mem_unitary
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    finiteIndexUnitaryEvolution energy ∈
      unitary
        (RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
          RHTower.FiniteIndexClockSpace (Fin (d + 1))) := by
  let _ : NormedAlgebra ℚ
      (RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
        RHTower.FiniteIndexClockSpace (Fin (d + 1))) :=
    .restrictScalars ℚ ℂ _
  unfold finiteIndexUnitaryEvolution
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff, star_smul,
    (finiteIndexDiagonalHamiltonian_isSelfAdjoint energy).star_eq]
  module

/-- Integer powers of the one-step unitary are the continuous Hamiltonian
evolution at integer times. -/
theorem finiteIndexUnitaryEvolution_pow_eq
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (n : ℕ) :
    (finiteIndexUnitaryEvolution energy) ^ n =
      exp ((n : ℝ) • ((-Complex.I) •
        RHTower.finiteIndexDiagonalHamiltonian energy)) := by
  let _ : NormedAlgebra ℚ
      (RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
        RHTower.FiniteIndexClockSpace (Fin (d + 1))) :=
    .restrictScalars ℚ ℂ _
  unfold finiteIndexUnitaryEvolution
  rw [← NormedSpace.exp_nsmul]
  congr 1
  module

/-- **Radial--angular future fan.** From one finite diagonal unitary record,
the same positive tolerance and finite horizons admit both:

* a strict-contraction completion whose every Heisenberg observable vanishes;
* a unitary completion of every prescribed positive temporal dimension.

Both branches are compared with the same reference Hamiltonian evolution in
operator norm, uniformly over every normalized observable. -/
theorem exists_finiteQuantumRecurrenceFutureFan
    {d k : ℕ} (hk : 0 < k) (hkd : k ≤ d)
    (energy : Fin (d + 1) → ℝ)
    (N : ℕ) (H η : ℝ) (hH : 0 ≤ H) (hη : 0 < η) :
    ∃ (r : ℝ) (perturbed : Fin (d + 1) → ℝ),
      0 < r ∧ r < 1 ∧
      ‖(r : ℂ) • finiteIndexUnitaryEvolution energy‖ < 1 ∧
      (∀ n ≤ N,
        ∀ O : RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
          RHTower.FiniteIndexClockSpace (Fin (d + 1)),
        ‖O‖ ≤ 1 →
        ‖(((r : ℂ) • finiteIndexUnitaryEvolution energy) ^ n) * O *
              star (((r : ℂ) • finiteIndexUnitaryEvolution energy) ^ n) -
            exp ((n : ℝ) • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian energy)) * O *
              star (exp ((n : ℝ) • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian energy)))‖ < η) ∧
      (∀ O : RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
          RHTower.FiniteIndexClockSpace (Fin (d + 1)),
        Tendsto
          (fun n =>
            (((r : ℂ) • finiteIndexUnitaryEvolution energy) ^ n) * O *
              star (((r : ℂ) • finiteIndexUnitaryEvolution energy) ^ n))
          atTop (𝓝 0)) ∧
      projectiveTemporalRank perturbed = k ∧
      (∀ i, dist (perturbed i) (energy i) < η / (2 * (H + 1))) ∧
      ∀ (O : RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
            RHTower.FiniteIndexClockSpace (Fin (d + 1)))
          (t : ℝ),
        ‖O‖ ≤ 1 → |t| ≤ H →
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian perturbed)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian perturbed))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian energy)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian energy)))‖ < η := by
  let U := finiteIndexUnitaryEvolution energy
  have hU := finiteIndexUnitaryEvolution_mem_unitary energy
  obtain ⟨r, hr0, hr1, hdamped, hradial, hextinct⟩ :=
    exists_scalarDampedUnitary_heisenberg_finiteHorizon_close_extinct
      U hU N η hη
  obtain ⟨perturbed, hrank, henergy, angular⟩ :=
    exists_finiteHorizonIndistinguishable_exactProjectiveTemporalRank
      hk hkd energy H η hH hη
  refine ⟨r, perturbed, hr0, hr1, hdamped, ?_, hextinct,
    hrank, henergy, angular⟩
  intro n hn O hO
  rw [← finiteIndexUnitaryEvolution_pow_eq energy n]
  exact hradial n hn O hO

end

end GaloisForLFunctions.HTGeometry
