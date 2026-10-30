import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching

/-!
# Spectral assembly at a fixed overlap

At a fixed width ratio `c`, three inputs determine the bottom of the complete Weil spectrum:

* a prime-defect reserve `a‖x‖² + b D_N(x) ≤ W_N(x)` with `b > 0`;
* norm quasimodes `‖W_N r̂_m - E_m r̂_m‖ → 0` for the normalized Ramanujan vectors;
* a common floor `e ≤ E_m` for every conductor.

The reserve bounds the defect on every energy sublevel, so one finite Ramanujan span carries a
fixed fraction of every low-energy unit vector. Each quasimode with `E_m` above a threshold
forces its coordinate to be small in the span of the eigenvectors below it. Together they exclude
every eigenvalue below `e`. This is the touching argument with the ratio held fixed; no inequality
about the size of `c` is used.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory

/-- A defect reserve gives one finite Ramanujan coordinate certificate on every energy sublevel. -/
theorem exists_finite_ramanujan_coordinate_certificate_of_reserve {φ : ℝ → ℝ} {c : ℝ}
    {a b : ℝ} (hb : 0 < b)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + b * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (T : ℝ) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → completeWeilEnergy φ c N x ≤ T →
          1 / 18 ≤ ∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le
    (max 0 ((T - a) / b)) (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨S, hS, ?_⟩
  filter_upwards [hres, eventually_normalizedRamanujanHorizonVector_gram_close S hS,
    eventually_ge_atTop 2] with N hresN hgram hN
  intro x hx henergy
  have hdef : poleDefect N (primeHorizonExtension x) ≤ max 0 ((T - a) / b) := by
    have h := hresN x
    rw [hx, one_pow, mul_one] at h
    have hd : poleDefect N (primeHorizonExtension x) ≤ (T - a) / b := by
      rw [le_div_iff₀ hb]
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

private theorem finite_residuals_small {φ : ℝ → ℝ} {c : ℝ} {E : ℕ → ℝ}
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ S,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  induction S using Finset.induction_on with
  | empty => exact Eventually.of_forall fun N m hm => False.elim (notMem_empty m hm)
  | @insert m S _ ih =>
      have hm : 0 < m := hS m (mem_insert_self m S)
      filter_upwards [(hquasi m hm).eventually (ge_mem_nhds hε),
        ih fun k hk => hS k (mem_insert_of_mem hk)] with N hmN hSN
      intro k hk
      rcases mem_insert.mp hk with rfl | hkS
      · exact hmN
      · exact hSN k hkS

/-- **Fixed-overlap spectral assembly.** A defect reserve, norm quasimodes and a common conductor
floor `e` put every complete-Weil eigenvalue eventually above every `b < e`. -/
theorem eventually_completeWeil_eigenvalues_ge_of_reserve_quasimodes {φ : ℝ → ℝ} {c : ℝ}
    {a β : ℝ} (hβ : 0 < β)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    {E : ℕ → ℝ}
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    {e : ℝ} (hfloor : ∀ m : ℕ, 0 < m → e ≤ E m) {b : ℝ} (hb : b < e) :
    ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N, b ≤ completeWeilEigenvalue φ c N i := by
  let δ := e - b
  have hδ : 0 < δ := sub_pos.mpr hb
  obtain ⟨S, hS, hcert⟩ := exists_finite_ramanujan_coordinate_certificate_of_reserve hβ hres b
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
  filter_upwards [hcert, finite_residuals_small hquasi hε S hS] with N hcertN hresN
  intro i
  by_contra hi
  let hA := completeWeilMatrix_isHermitian φ c N
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
  have henergy : completeWeilEnergy φ c N x ≤ b := by
    have h := HTGeometry.hermitianEnergy_le_of_support hA b x hlo
    simpa only [completeWeilEnergy, hnorm, one_pow, mul_one] using h
  have hmass := hcertN x hnorm henergy
  have hsum : (∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
      (S.card : ℝ) * ε ^ 2 / δ ^ 2 := by
    have hterm : ∀ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤ ε ^ 2 / δ ^ 2 := by
      intro m hm
      have hE := hfloor m (hS m hm)
      have hgap : δ ≤ E m - b := by dsimp only [δ]; linarith only [hE]
      have hgt : b < E m := by linarith only [hgap, hδ]
      have hlow := HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq hA b (E m) hgt x
        (normalizedRamanujanHorizonVector m N) hnorm hlo
      have hr := hresN m hm
      have hrsq := mul_self_le_mul_self (norm_nonneg _) hr
      have hgsq := mul_self_le_mul_self hδ.le hgap
      rw [← sq, ← sq] at hrsq hgsq
      calc
        _ ≤ _ := hlow
        _ ≤ ε ^ 2 / (E m - b) ^ 2 := div_le_div_of_nonneg_right hrsq (sq_nonneg _)
        _ ≤ ε ^ 2 / δ ^ 2 := div_le_div_of_nonneg_left (sq_nonneg ε) (sq_pos_of_pos hδ) hgsq
    have h := sum_le_sum hterm
    simpa only [sum_const, nsmul_eq_mul, mul_div_assoc] using h
  linarith only [hmass, hsum, hcost]

/-- The same assembly gives positive definiteness when the floor is positive. -/
theorem eventually_completeWeilMatrix_posDef_of_reserve_quasimodes {φ : ℝ → ℝ} {c : ℝ}
    {a β : ℝ} (hβ : 0 < β)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    {E : ℕ → ℝ}
    (hquasi : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    {e : ℝ} (he : 0 < e) (hfloor : ∀ m : ℕ, 0 < m → e ≤ E m) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix φ c N).PosDef := by
  filter_upwards [eventually_completeWeil_eigenvalues_ge_of_reserve_quasimodes hβ hres hquasi
    hfloor (half_lt_self he)] with N hN
  exact (completeWeilMatrix_isHermitian φ c N).posDef_iff_eigenvalues_pos.mpr fun i =>
    lt_of_lt_of_le (half_pos he) (hN i)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
