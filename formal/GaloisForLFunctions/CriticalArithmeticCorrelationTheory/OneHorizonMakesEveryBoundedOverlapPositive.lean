import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedOverlapKeepsACompleteWeilReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorQuasimodesAreUniformOnBoundedOverlap

/-!
# One horizon makes every bounded overlap positive

For the explicit tilted spline, a common complete defect reserve confines all low-energy
vectors to one finite conductor family. Uniform actual norm quasimodes and the positive
Fourier tail beyond the maximal overlap exclude every low eigenvalue at one horizon.
The endpoint identity joins this estimate to uniform positivity through touching.

The spectral floor controls every signed atomic packet for all `0 < c ≤ K` simultaneously.
The bound `K` is fixed; no prescribed unbounded overlap schedule is asserted.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-- A common defect reserve forces definite coordinate mass in one fixed finite conductor family. -/
private theorem exists_tiltedUnitSpline_uniform_coordinate_certificate {K : ℝ} (hK : 1 ≤ K) (T : ℝ) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → completeWeilEnergy tiltedUnitSpline c N x ≤ T →
          1 / 18 ≤ ∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_uniform_overlap_reserve hK
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le
    (max 0 ((T - a) / β)) (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨S, hS, ?_⟩
  filter_upwards [hres, eventually_normalizedRamanujanHorizonVector_gram_close S hS,
    eventually_ge_atTop 2] with N hresN hgram hN
  intro c hc1 hcK x hx henergy
  have hdef : poleDefect N (primeHorizonExtension x) ≤ max 0 ((T - a) / β) := by
    have h := hresN c hc1 hcK x
    rw [hx, one_pow, mul_one] at h
    have hd : poleDefect N (primeHorizonExtension x) ≤ (T - a) / β := by
      rw [le_div_iff₀ hβ]
      linarith only [h, henergy]
    exact hd.trans (le_max_right _ _)
  obtain ⟨a', ha'⟩ := happ N (primeHorizonExtension x)
    (by rw [sum_primeHorizonExtension_sq, hx]; norm_num) hdef
  have happN : ‖x - ∑ m ∈ S, a' m • ramanujanHorizonVector m N‖ ^ 2 ≤ 1 / 4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [← sum_coe_sort (Icc 1 N) (fun n =>
      (primeHorizonExtension x n - ∑ m ∈ S, a' m * ramanujanPoleProfile m n) ^ 2)] at ha'
    convert ha' using 1
    apply sum_congr rfl
    intro n _
    have hsum : (∑ m ∈ S, a' m • ramanujanHorizonVector m N) n =
        ∑ m ∈ S, a' m * ramanujanPoleProfile m n := by
      change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
        (∑ m ∈ S, a' m • ramanujanHorizonVector m N) = _
      rw [map_sum]
      exact sum_congr rfl fun m _ => rfl
    simp only [PiLp.sub_apply, hsum, primeHorizonExtension_coe]
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  let w : S → ℝ := fun m => a' m * Real.sqrt (Real.log N)
  have heq : (∑ m : S, w m • normalizedRamanujanHorizonVector m N) =
      ∑ m ∈ S, a' m • ramanujanHorizonVector m N := by
    rw [← sum_coe_sort S (fun m => a' m • ramanujanHorizonVector m N)]
    refine sum_congr rfl fun m _ => ?_
    rw [normalizedRamanujanHorizonVector, smul_smul]
    congr 1
    dsimp only [w]
    field_simp
  have hcert := HTGeometry.coordinate_mass_ge_of_finite_approximation
    (fun m : S => normalizedRamanujanHorizonVector m N) hgram x hx w
    (by rw [heq]; exact happN)
  simpa only [sum_coe_sort S (fun m => ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2)] using hcert

/-- A finite conductor family shares the same bounded-overlap residual horizon. -/
private theorem finite_tiltedUnitSpline_uniform_quasimodes {K : ℝ} (hK : 1 ≤ K)
    {ε : ℝ} (hε : 0 < ε) (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ S, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  induction S using Finset.induction_on with
  | empty => exact Eventually.of_forall fun N m hm => False.elim (notMem_empty m hm)
  | @insert m S _ ih =>
      have hm : 0 < m := hS m (mem_insert_self m S)
      filter_upwards [eventually_tiltedUnitSpline_completedConductor_residual_uniform_overlap hK hm hε,
        ih fun k hk => hS k (mem_insert_of_mem hk)] with N hmN hSN
      intro k hk
      rcases mem_insert.mp hk with rfl | hkS
      · exact hmN
      · exact hSN k hkS

/-- The tail beyond the maximal overlap is a common positive floor for every completed conductor. -/
theorem tiltedUnitSpline_completedConductorEnergy_ge_boundedOverlapTail {K c : ℝ}
    (hc : 0 < c) (hcK : c ≤ K) {m : ℕ} (hm : 0 < m) :
    2 / (∫ u, tiltedUnitSpline u ^ 2) * ∫ t in Set.Ioi K, shellSpectrum tiltedUnitSpline t ≤
      completedConductorEnergy tiltedUnitSpline c m := by
  have htail : (∫ t in Set.Ioi K, shellSpectrum tiltedUnitSpline t) ≤
      ∫ t in Set.Ioi c, shellSpectrum tiltedUnitSpline t :=
    setIntegral_mono_set
      (integrableOn_shellSpectrum_Ioi contDiff_tiltedUnitSpline hasCompactSupport_tiltedUnitSpline c)
      (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Eventually.of_forall (Set.Ioi_subset_Ioi hcK))
  exact (mul_le_mul_of_nonneg_left htail
    (div_nonneg zero_le_two integral_tiltedUnitSpline_sq_pos.le)).trans
      (completedConductorEnergy_ge_shellTail contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
        integral_tiltedUnitSpline_sq_pos hc hm)

/-- Every threshold below the common tail floor bounds the literal spectrum at one bounded-overlap horizon. -/
theorem eventually_tiltedUnitSpline_eigenvalues_ge_uniformly_above_touching {K : ℝ} (hK : 1 ≤ K)
    {b : ℝ} (hb : b < 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      ∫ t in Set.Ioi K, shellSpectrum tiltedUnitSpline t) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ∀ i : PrimeHorizonIndex N, b ≤ completeWeilEigenvalue tiltedUnitSpline c N i := by
  let e := 2 / (∫ u, tiltedUnitSpline u ^ 2) * ∫ t in Set.Ioi K, shellSpectrum tiltedUnitSpline t
  let δ := e - b
  have hδ : 0 < δ := sub_pos.mpr hb
  obtain ⟨S, hS, hcert⟩ := exists_tiltedUnitSpline_uniform_coordinate_certificate hK b
  let ε := δ / (6 * ((S.card : ℝ) + 1))
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hcost : (S.card : ℝ) * ε ^ 2 / δ ^ 2 < 1 / 18 := by
    have heq : (S.card : ℝ) * ε ^ 2 / δ ^ 2 =
        (S.card : ℝ) / (36 * ((S.card : ℝ) + 1) ^ 2) := by
      dsimp only [ε]
      field_simp [hδ.ne', show (S.card : ℝ) + 1 ≠ 0 by positivity]
      ring
    rw [heq, div_lt_iff₀ (by positivity)]
    nlinarith only [hcard, sq_nonneg (S.card : ℝ)]
  filter_upwards [hcert, finite_tiltedUnitSpline_uniform_quasimodes hK hε S hS] with N hcertN hresN
  intro c hc1 hcK i
  have hc : 0 < c := zero_lt_one.trans_le hc1
  by_contra hi
  let hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have hi' : hA.eigenvalues i < b := lt_of_not_ge hi
  let x := hA.eigenvectorBasis i
  have hnorm : ‖x‖ = 1 := by
    have h : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith only [h, norm_nonneg x]
  have hlo : ∀ j, b ≤ hA.eigenvalues j → ⟪x, hA.eigenvectorBasis j⟫ = 0 := by
    intro j hj
    have hij : i ≠ j := by
      intro hij
      subst j
      exact (not_le_of_gt hi') hj
    simpa only [if_neg hij] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  have henergy : completeWeilEnergy tiltedUnitSpline c N x ≤ b := by
    have h := HTGeometry.hermitianEnergy_le_of_support hA b x hlo
    simpa only [completeWeilEnergy, hnorm, one_pow, mul_one] using h
  have hmass := hcertN c hc1 hcK x hnorm henergy
  have hsum : (∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
      (S.card : ℝ) * ε ^ 2 / δ ^ 2 := by
    have hterm : ∀ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤ ε ^ 2 / δ ^ 2 := by
      intro m hm
      have hE := tiltedUnitSpline_completedConductorEnergy_ge_boundedOverlapTail hc hcK (hS m hm)
      have hgap : δ ≤ completedConductorEnergy tiltedUnitSpline c m - b := by
        dsimp only [δ, e]
        linarith only [hE]
      have hgt : b < completedConductorEnergy tiltedUnitSpline c m := by linarith only [hgap, hδ]
      have hlow := HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq hA b
        (completedConductorEnergy tiltedUnitSpline c m) hgt x (normalizedRamanujanHorizonVector m N) hnorm hlo
      have hr := hresN m hm c hc1 hcK
      have hrsq := mul_self_le_mul_self (norm_nonneg _) hr
      have hgsq := mul_self_le_mul_self hδ.le hgap
      rw [← sq, ← sq] at hrsq hgsq
      calc
        _ ≤ _ := hlow
        _ ≤ ε ^ 2 / (completedConductorEnergy tiltedUnitSpline c m - b) ^ 2 :=
          div_le_div_of_nonneg_right hrsq (sq_nonneg _)
        _ ≤ ε ^ 2 / δ ^ 2 := div_le_div_of_nonneg_left (sq_nonneg ε) (sq_pos_of_pos hδ) hgsq
    have h := sum_le_sum hterm
    simpa only [sum_const, nsmul_eq_mul, mul_div_assoc] using h
  linarith only [hmass, hsum, hcost]

private theorem completedConductorEnergy_endpoint_shape (φ : ℝ → ℝ) :
    completedConductorEnergy φ 1 1 =
      bumpRobin φ 1 / (∫ u, φ u ^ 2) + completeWeilPoleShift φ 1 - Real.log (2 * Real.pi) := by
  have hcorr : shellCorrection φ 1 1 = 0 := by
    simp only [shellCorrection, Nat.ceil_one, Ico_self, sum_empty, mul_zero]
  rw [completedConductorEnergy_eq_sub_shellCorrection zero_lt_one zero_lt_one, hcorr, sub_zero,
    completeWeilAdjunctionEnergy, SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_one,
    if_pos rfl, completeWeilSelfFinitePart, mul_one,
    Real.log_div one_ne_zero (by positivity), Real.log_one]
  ring

/-- One positive spectral floor and one horizon control every overlap bounded by `K`,
including arbitrarily small positive overlap and passage through touching. -/
theorem exists_tiltedUnitSpline_completeWeil_uniform_boundedOverlap_floor (K : ℝ) :
    ∃ e : ℝ, 0 < e ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ∀ i : PrimeHorizonIndex N, e ≤ completeWeilEigenvalue tiltedUnitSpline c N i := by
  let L := max 1 K
  have hL : 1 ≤ L := le_max_left _ _
  let e := 2 / (∫ u, tiltedUnitSpline u ^ 2) * ∫ t in Set.Ioi L, shellSpectrum tiltedUnitSpline t
  have he : 0 < e := mul_pos (div_pos zero_lt_two integral_tiltedUnitSpline_sq_pos)
    (integral_shellSpectrum_tiltedUnitSpline_pos L)
  have hendpoint : e ≤ bumpRobin tiltedUnitSpline 1 / (∫ u, tiltedUnitSpline u ^ 2) +
      completeWeilPoleShift tiltedUnitSpline 1 - Real.log (2 * Real.pi) := by
    rw [← completedConductorEnergy_endpoint_shape]
    exact tiltedUnitSpline_completedConductorEnergy_ge_boundedOverlapTail zero_lt_one hL zero_lt_one
  have hb : e / 2 < bumpRobin tiltedUnitSpline 1 / (∫ u, tiltedUnitSpline u ^ 2) +
      completeWeilPoleShift tiltedUnitSpline 1 - Real.log (2 * Real.pi) :=
    (half_lt_self he).trans_le hendpoint
  refine ⟨e / 2, half_pos he, ?_⟩
  filter_upwards [eventually_tiltedUnitSpline_eigenvalues_ge_uniformly_above_touching hL (half_lt_self he),
    eventually_completeWeil_eigenvalues_ge_uniformly_at_touching contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hb] with N habove hbelow
  intro c hc hcK i
  by_cases hc1 : c ≤ 1
  · exact hbelow c hc hc1 i
  · exact habove c (le_of_not_ge hc1) (hcK.trans (le_max_right _ _)) i

/-- Every bounded moving overlap has positive definite literal complete Weil matrices beyond one horizon. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_uniform_boundedOverlap (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  obtain ⟨e, he, hfloor⟩ := exists_tiltedUnitSpline_completeWeil_uniform_boundedOverlap_floor K
  filter_upwards [hfloor] with N hN
  intro c hc hcK
  exact (completeWeilMatrix_isHermitian tiltedUnitSpline c N).posDef_iff_eigenvalues_pos.mpr
    fun i => he.trans_le (hN c hc hcK i)

/-- The common positive spectral floor controls every signed coefficient vector. -/
theorem exists_tiltedUnitSpline_completeWeilEnergy_uniform_boundedOverlap_floor (K : ℝ) :
    ∃ e : ℝ, 0 < e ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        e * ‖x‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨e, he, hfloor⟩ := exists_tiltedUnitSpline_completeWeil_uniform_boundedOverlap_floor K
  refine ⟨e, he, ?_⟩
  filter_upwards [hfloor] with N hN
  intro c hc hcK x
  rw [completeWeilEnergy,
    HTGeometry.hermitianEnergy_eq_sum (completeWeilMatrix_isHermitian tiltedUnitSpline c N),
    ← (completeWeilMatrix_isHermitian tiltedUnitSpline c N).eigenvectorBasis.sum_sq_inner_left x, mul_sum]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hN c hc hcK i) (sq_nonneg _)

/-- The actual complete Weil functional is nonnegative on every signed atomic packet,
with a single horizon for the whole bounded overlap interval. -/
theorem eventually_tiltedUnitSpline_weilQuad_nonneg_uniform_boundedOverlap (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K → ∀ y : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N y (atomDilate tiltedUnitSpline (c / N))) := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilMatrix_posDef_uniform_boundedOverlap K,
    eventually_ge_atTop 1] with N hpos hN
  intro c hc hcK y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hM : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcK)
  have hquad : 0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (horizonProfileVector y N), horizonProfileVector y N⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hN] at hquad
  have htest : atomicTest N (primeHorizonExtension (horizonProfileVector y N))
      (atomDilate tiltedUnitSpline (c / N)) =
      atomicTest N y (atomDilate tiltedUnitSpline (c / N)) := by
    funext u
    unfold atomicTest
    apply sum_congr rfl
    intro n hn
    have hcoe : primeHorizonExtension (horizonProfileVector y N) n = y n :=
      primeHorizonExtension_coe (horizonProfileVector y N) ⟨n, hn⟩
    rw [hcoe]
  rw [htest, div_nonneg_iff] at hquad
  rcases hquad with ⟨hq, -⟩ | ⟨-, hneg⟩
  · exact hq
  · linarith only [hM, hneg]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeil_uniform_boundedOverlap_floor
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_uniform_boundedOverlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilEnergy_uniform_boundedOverlap_floor
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_weilQuad_nonneg_uniform_boundedOverlap
