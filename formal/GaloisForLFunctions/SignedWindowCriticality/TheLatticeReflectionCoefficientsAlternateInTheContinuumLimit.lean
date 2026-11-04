import GaloisForLFunctions.SignedWindowCriticality.TheJetMinorsArePositiveOnEveryNonnegativeWindow
import GaloisForLFunctions.GrowingWindowsOfSpecZ.RefiningTheLatticeLowersTheMargin
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# The lattice reflection coefficients alternate in the continuum limit

The lattice canonical system of a bump `φ` at step `h` is the Levinson (Szegő) recursion of the
Weil sequence `κ_h(d) = W(φ, φ(· + dh))`, with margins `E_n(h)` and reflection coefficients
`γ_n(h)`, `E_{n+1} = E_n(1 − γ_n²)`. Its rescaled margins converge to the jet Hankel system,
`h^{−2n}E_n → e_n = det J_{n+1}/det J_n` (`tendsto_levinsonErr_div_pow`). This module computes the
limit of the reflection coefficients themselves.

* **Newton's formula on a lattice** (`latticeTest_eq_sum_diffQuot`): a lattice test
  `Σ_k x_kφ(· + kh)` is `Σ_j b_jh^j·Δ_h^jφ/h^j` with `b_j = Σ_k C(k, j)x_k`, and
  `Σ_j (−1)^j b_j = x_0` (`sum_neg_one_pow_mul_newtonCoeff`).
* **The coefficients alternate** (`tendsto_reflCoeff_neg_one_pow`): if the jet Gram of size `n + 2`
  is positive definite, `γ_n(φ, h) → (−1)^n` as `h → 0⁺`. The Levinson vector `(1, a^{(n+1)})` has
  energy `E_{n+1} = O(h^{2n+2})`; coercivity of the jet Gram, transferred to the difference Gram,
  forces its Newton coefficients `b_j = O(h)` for `j ≤ n`, and `Σ_j (−1)^j b_j = 1` pins the top one,
  `b_{n+1} = −γ_n`, at `(−1)^{n+1}`: the Levinson vector becomes the forward difference
  `(−1)^{n+1}Δ^{n+1}`.
* **The defect is the continuum Jacobi parameter** (`tendsto_one_sub_reflCoeff_sq_div_sq`):
  `(1 − γ_n²)/h² → e_{n+1}/e_n`.
* **On every nonnegative window, and unconditionally on the base window**
  (`reflCoeff_continuumLimit_of_window_nonneg`, `reflCoeff_continuumLimit_of_base`): both limits
  hold for every nonzero smooth bump, with `e_{n+1}/e_n > 0`.

So under refinement the lattice canonical system of every bump freezes onto the alternating boundary
points `(−1)^n` of the Schur disk and stays off it only at order `h²`, with the ratios
`e_{n+1}/e_n` of the jet system as normal velocities.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Matrix

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis DimensionZeroGeometryOfSpecZ
open GrowingWindowsOfSpecZ

variable {φ : ℝ → ℝ}

/-! ### Newton's formula on a lattice -/

/-- **Newton's forward-difference formula for a lattice test**:
`Σ_k x_kφ(· + kh) = Σ_j b_jΔ_h^jφ` with `b_j = Σ_k C(k, j)x_k`. -/
theorem latticeTest_eq_sum_fwdDiff (φ : ℝ → ℝ) (h : ℝ) {N : ℕ} (x : Fin N → ℝ) :
    latticeTest φ h x =
      ∑ j : Fin N, (∑ k : Fin N, ((k : ℕ).choose j : ℝ) * x k) • (fwdDiff h)^[j] φ := by
  funext u
  rw [latticeTest_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hN : ∀ k : Fin N, φ (u + (k : ℕ) * h) =
      ∑ j : Fin N, ((k : ℕ).choose j : ℝ) * (fwdDiff h)^[j] φ u := by
    intro k
    have h1 := shift_eq_sum_fwdDiff_iter (h := h) φ (k : ℕ) u
    rw [nsmul_eq_mul] at h1
    have h2 : ∑ j : Fin N, ((k : ℕ).choose j : ℝ) * (fwdDiff h)^[j] φ u =
        ∑ j ∈ Finset.range N, ((k : ℕ).choose j : ℝ) * (fwdDiff h)^[j] φ u :=
      (Finset.sum_range (fun j => ((k : ℕ).choose j : ℝ) * (fwdDiff h)^[j] φ u)).symm
    rw [h2, h1]
    simp only [nsmul_eq_mul]
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt k.isLt)) fun j _ hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  simp only [hN, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem fwdDiff_iter_eq_smul_diffQuot {h : ℝ} (hh : h ≠ 0) (k : ℕ) :
    (fwdDiff h)^[k] φ = h ^ k • diffQuot φ h k := by
  funext u
  simp only [diffQuot, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The Newton coefficients `b_j = Σ_k C(k, j)x_k` of a lattice amplitude vector. -/
def newtonCoeff {N : ℕ} (x : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∑ k : Fin N, ((k : ℕ).choose j : ℝ) * x k

theorem latticeTest_eq_sum_diffQuot {h : ℝ} (hh : h ≠ 0) {N : ℕ} (x : Fin N → ℝ) :
    latticeTest φ h x = ∑ j : Fin N, (newtonCoeff x j * h ^ (j : ℕ)) • diffQuot φ h j := by
  rw [latticeTest_eq_sum_fwdDiff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fwdDiff_iter_eq_smul_diffQuot hh, smul_smul, newtonCoeff]

/-- Evaluating Newton's formula at `τ = 0`: `Σ_j (−1)^j b_j = x_0`. -/
theorem sum_neg_one_pow_mul_newtonCoeff {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * newtonCoeff x j = x 0 := by
  have hk : ∀ k : Fin (n + 1),
      ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * ((k : ℕ).choose j : ℝ) =
        if (k : ℕ) = 0 then 1 else 0 := by
    intro k
    have h2 : ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * ((k : ℕ).choose j : ℝ) =
        ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * ((k : ℕ).choose j : ℝ) :=
      (Finset.sum_range (fun j => (-1 : ℝ) ^ j * ((k : ℕ).choose j : ℝ))).symm
    have h3 : ∑ j ∈ Finset.range ((k : ℕ) + 1), (-1 : ℝ) ^ j * ((k : ℕ).choose j : ℝ) =
        ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * ((k : ℕ).choose j : ℝ) := by
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt k.isLt))
        fun j _ hj => ?_
      rw [Finset.mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    have h4 := congrArg (Int.cast : ℤ → ℝ) (Int.alternating_sum_range_choose (n := (k : ℕ)))
    push_cast at h4
    rw [h2, ← h3, h4]
  unfold newtonCoeff
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ k : Fin (n + 1), ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * (((k : ℕ).choose j : ℝ) * x k) =
      (if (k : ℕ) = 0 then 1 else 0) * x k := fun k => by
    rw [← hk k, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [this]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk0
    have : (k : ℕ) ≠ 0 := fun h => hk0 (Fin.ext h)
    simp [this]
  · simp

theorem newtonCoeff_last {n : ℕ} (x : Fin (n + 2) → ℝ) :
    newtonCoeff x (Fin.last (n + 1)) = x (Fin.last (n + 1)) := by
  unfold newtonCoeff
  rw [Finset.sum_eq_single (Fin.last (n + 1))]
  · simp
  · intro k _ hk
    rw [Nat.choose_eq_zero_of_lt (by simpa using Fin.val_lt_last hk), Nat.cast_zero, zero_mul]
  · simp

/-! ### The Levinson vector in the difference basis -/

theorem levinsonVec_last (κ : ℤ → ℝ) (n : ℕ) :
    levinsonVec κ (n + 1) (Fin.last (n + 1)) = -reflCoeff κ n := by
  rw [levinsonVec, ← Fin.succ_last, Fin.cons_succ, levinsonPred_succ, Fin.snoc_last]

theorem levinsonVec_zero' (κ : ℤ → ℝ) (n : ℕ) : levinsonVec κ n 0 = 1 := by
  rw [levinsonVec, Fin.cons_zero]

/-- Weil's form on a combination of normalized differences is the Gram form of `diffGram`. -/
theorem weilQuad_sum_diffQuot (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (h : ℝ) {N : ℕ}
    (y : Fin N → ℝ) :
    weilQuad (∑ j : Fin N, y j • diffQuot φ h j) = y ⬝ᵥ diffGram φ h N *ᵥ y := by
  have := weilPair_sum_smul_sum_smul (f := fun j : Fin N => diffQuot φ h j)
    (fun j => diffQuot_mem_realTests hφ hφc h j) y
  show weilPair _ _ = _
  rw [this]
  simp only [dotProduct, Matrix.mulVec, diffGram, Matrix.of_apply]

/-! ### The reflection coefficients freeze on the alternating boundary of the Schur disk -/

theorem eventually_levinsonErr_pos (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (k : ℕ)
    (hJ : ∀ i ≤ k + 1, (jetGram φ i).PosDef) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < levinsonErr (weilSeq φ h) k := by
  have hlim := tendsto_levinsonErr_div_pow hφ hφc k fun i hi => (hJ (i + 1) (by omega)).det_pos.ne'
  have hpos : 0 < (jetGram φ (k + 1)).det / (jetGram φ k).det :=
    div_pos (hJ _ le_rfl).det_pos (hJ _ (by omega)).det_pos
  filter_upwards [hlim.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with h h1 h2
  have hp : 0 < h ^ (2 * k) := pow_pos h2 _
  have := mul_pos h1 hp
  rwa [div_mul_cancel₀ _ hp.ne'] at this

/-- **The lattice reflection coefficients alternate in the continuum limit**: for a smooth bump
whose jet minors up to size `n + 2` are positive, `γ_n(φ, h) → (−1)^n` as `h → 0⁺`. -/
theorem tendsto_reflCoeff_neg_one_pow (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (n : ℕ)
    (hJ : ∀ k ≤ n + 2, (jetGram φ k).PosDef) :
    Tendsto (fun h => reflCoeff (weilSeq φ h) n) (𝓝[>] 0) (𝓝 ((-1) ^ n)) := by
  have hφr : φ ∈ realTests := by simpa using iteratedDeriv_mem_realTests hφ hφc 0
  -- coercivity of the jet Gram, transferred to the difference Gram
  obtain ⟨μ, hμ, hcoer⟩ := GaloisForLFunctions.HTGeometry.posDef_coercive (hJ (n + 2) le_rfl)
  have hent : ∀ p q : Fin (n + 2),
      Tendsto (fun h => diffGram φ h (n + 2) p q) (𝓝[>] 0) (𝓝 (jetGram φ (n + 2) p q)) := by
    intro p q
    simpa [diffGram, jetGram] using tendsto_weilPair_diffQuot hφ hφc p q
  set ε : ℝ := μ / (2 * (n + 2 : ℕ)) with hεdef
  have hεpos : 0 < ε := by positivity
  have hclose : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ p q : Fin (n + 2),
      |diffGram φ h (n + 2) p q - jetGram φ (n + 2) p q| ≤ ε := by
    rw [eventually_all]; intro p; rw [eventually_all]; intro q
    filter_upwards [(hent p q).eventually (Metric.closedBall_mem_nhds _ hεpos)] with h hh
    rwa [Real.dist_eq] at hh
  have hlow : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ y : Fin (n + 2) → ℝ,
      μ / 2 * (y ⬝ᵥ y) ≤ y ⬝ᵥ diffGram φ h (n + 2) *ᵥ y := by
    filter_upwards [hclose] with h hh y
    have h1 := GaloisForLFunctions.HTGeometry.abs_dotProduct_mulVec_le
      (diffGram φ h (n + 2) - jetGram φ (n + 2)) hεpos.le (fun p q => by simpa using hh p q) y
    have hNε : ((n + 2 : ℕ) : ℝ) * ε = μ / 2 := by rw [hεdef]; field_simp
    rw [hNε] at h1
    have hsplit : y ⬝ᵥ diffGram φ h (n + 2) *ᵥ y = y ⬝ᵥ jetGram φ (n + 2) *ᵥ y +
        y ⬝ᵥ (diffGram φ h (n + 2) - jetGram φ (n + 2)) *ᵥ y := by
      rw [Matrix.sub_mulVec, dotProduct_sub]; ring
    have h2 := hcoer y
    rw [hsplit]
    linarith [(abs_le.mp h1).1]
  -- the last margin is born at order h^{2(n+1)}
  set e := (jetGram φ (n + 2)).det / (jetGram φ (n + 1)).det
  have hlimE := tendsto_levinsonErr_div_pow hφ hφc (n + 1)
    fun i hi => (hJ (i + 1) (by omega)).det_pos.ne'
  have hup : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      levinsonErr (weilSeq φ h) (n + 1) / h ^ (2 * (n + 1)) < e + 1 :=
    hlimE.eventually (gt_mem_nhds (by linarith))
  have hEk : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ k : Fin (n + 2), 0 < levinsonErr (weilSeq φ h) k :=
    eventually_all.mpr fun k => eventually_levinsonErr_pos hφ hφc k fun i hi => hJ i (by omega)
  have hlt1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  have he : 0 < e := div_pos (hJ (n + 2) le_rfl).det_pos (hJ (n + 1) (by omega)).det_pos
  set C : ℝ := 2 / μ * (e + 1)
  have hC0 : 0 ≤ C := by positivity
  -- every Newton coefficient below the top one is `O(h)`
  have hsmall : ∀ j : Fin (n + 1), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      |newtonCoeff (levinsonVec (weilSeq φ h) (n + 1)) (Fin.castSucc j)| ≤ Real.sqrt C * h := by
    intro j
    filter_upwards [hlow, hup, hEk, hlt1, self_mem_nhdsWithin] with h hlo hu hE h1 h0
    have h0' : 0 < h := h0
    set v := levinsonVec (weilSeq φ h) (n + 1)
    set y : Fin (n + 2) → ℝ := fun i => newtonCoeff v i * h ^ (i : ℕ)
    have hEq : levinsonErr (weilSeq φ h) (n + 1) = y ⬝ᵥ diffGram φ h (n + 2) *ᵥ y := by
      rw [← toeplitzForm_levinsonVec (weilSeq_isEven φ h) fun k hk => (hE ⟨k, by omega⟩).ne',
        ← weilQuad_latticeTest hφr, latticeTest_eq_sum_diffQuot h0'.ne',
        weilQuad_sum_diffQuot hφ hφc]
    have hpow : 0 < h ^ (2 * (n + 1)) := pow_pos h0' _
    have hyy : y ⬝ᵥ y ≤ C * h ^ (2 * (n + 1)) := by
      have hb : levinsonErr (weilSeq φ h) (n + 1) < (e + 1) * h ^ (2 * (n + 1)) := by
        rwa [div_lt_iff₀ hpow] at hu
      have h3 := hlo y
      rw [← hEq] at h3
      have h4 : μ * (y ⬝ᵥ y) ≤ μ * (C * h ^ (2 * (n + 1))) := by
        have : μ * (C * h ^ (2 * (n + 1))) = 2 * ((e + 1) * h ^ (2 * (n + 1))) := by
          simp only [C]; field_simp
        rw [this]; linarith
      exact le_of_mul_le_mul_left h4 hμ
    have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
    set b := newtonCoeff v (Fin.castSucc j)
    have hyj : y (Fin.castSucc j) * y (Fin.castSucc j) ≤ y ⬝ᵥ y := by
      have := Finset.single_le_sum (f := fun i => y i * y i) (fun i _ => mul_self_nonneg (y i))
        (Finset.mem_univ (Fin.castSucc j))
      simpa [dotProduct] using this
    have hy' : y (Fin.castSucc j) = b * h ^ (j : ℕ) := by simp [y, b]
    have hsplitpow : h ^ (2 * (n + 1)) = (h ^ (j : ℕ)) ^ 2 * h ^ (2 * (n + 1 - j)) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have hhj : 0 < (h ^ (j : ℕ)) ^ 2 := by positivity
    have hb2 : b ^ 2 ≤ C * h ^ (2 * (n + 1 - j)) := by
      have h5 := hyj.trans hyy
      rw [hy', hsplitpow] at h5
      have h6 : b ^ 2 * (h ^ (j : ℕ)) ^ 2 ≤ C * h ^ (2 * (n + 1 - j)) * (h ^ (j : ℕ)) ^ 2 := by
        nlinarith
      exact le_of_mul_le_mul_right h6 hhj
    have hh2 : h ^ (2 * (n + 1 - j)) ≤ h ^ 2 := pow_le_pow_of_le_one h0'.le h1.le (by omega)
    have hb2' : b ^ 2 ≤ C * h ^ 2 := hb2.trans (mul_le_mul_of_nonneg_left hh2 hC0)
    calc |b| ≤ Real.sqrt (C * h ^ 2) := Real.abs_le_sqrt hb2'
      _ = Real.sqrt C * h := by rw [Real.sqrt_mul hC0, Real.sqrt_sq h0'.le]
  have hb0 : ∀ j : Fin (n + 1), Tendsto
      (fun h => newtonCoeff (levinsonVec (weilSeq φ h) (n + 1)) (Fin.castSucc j)) (𝓝[>] 0)
      (𝓝 0) := by
    intro j
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (hsmall j) ?_
    have : Tendsto (fun h : ℝ => Real.sqrt C * h) (𝓝 0) (𝓝 (Real.sqrt C * 0)) :=
      tendsto_id.const_mul _
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- the top coefficient is `−γ_n`, and the Newton coefficients sum to `1` with alternating signs
  have key : ∀ h, reflCoeff (weilSeq φ h) n = (-1) ^ n * (1 - ∑ j : Fin (n + 1),
      (-1) ^ (j : ℕ) * newtonCoeff (levinsonVec (weilSeq φ h) (n + 1)) (Fin.castSucc j)) := by
    intro h
    have hs := sum_neg_one_pow_mul_newtonCoeff (levinsonVec (weilSeq φ h) (n + 1))
    rw [Fin.sum_univ_castSucc, newtonCoeff_last, levinsonVec_last, levinsonVec_zero'] at hs
    simp only [Fin.val_castSucc, Fin.val_last] at hs
    have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [pow_succ] at hs
    linear_combination (-1 : ℝ) ^ n * hs - reflCoeff (weilSeq φ h) n * hsq
  have hlim := tendsto_const_nhds (x := ((-1 : ℝ) ^ n)) |>.mul (tendsto_const_nhds (x := (1 : ℝ)) |>.sub
    (tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1))) fun j _ => (hb0 j).const_mul
      ((-1 : ℝ) ^ (j : ℕ))))
  simp only [mul_zero, Finset.sum_const_zero, sub_zero, mul_one] at hlim
  exact hlim.congr fun h => (key h).symm

/-- **The defect of the reflection coefficients is the continuum Jacobi parameter**:
`(1 − γ_n(φ, h)²)/h² → e_{n+1}/e_n`, `e_k = det J_{k+1}/det J_k`. -/
theorem tendsto_one_sub_reflCoeff_sq_div_sq (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (n : ℕ) (hJ : ∀ k ≤ n + 2, (jetGram φ k).PosDef) :
    Tendsto (fun h => (1 - reflCoeff (weilSeq φ h) n ^ 2) / h ^ 2) (𝓝[>] 0)
      (𝓝 (((jetGram φ (n + 2)).det / (jetGram φ (n + 1)).det) /
        ((jetGram φ (n + 1)).det / (jetGram φ n).det))) := by
  have h1 := tendsto_levinsonErr_div_pow hφ hφc (n + 1)
    fun i hi => (hJ (i + 1) (by omega)).det_pos.ne'
  have h0 := tendsto_levinsonErr_div_pow hφ hφc n fun i hi => (hJ (i + 1) (by omega)).det_pos.ne'
  have hne : (jetGram φ (n + 1)).det / (jetGram φ n).det ≠ 0 :=
    (div_pos (hJ (n + 1) (by omega)).det_pos (hJ n (by omega)).det_pos).ne'
  refine (h1.div h0 hne).congr' ?_
  filter_upwards [eventually_levinsonErr_pos hφ hφc n fun i hi => hJ i (by omega),
    self_mem_nhdsWithin] with h hE hh
  have hh' : (h : ℝ) ≠ 0 := (show (0 : ℝ) < h from hh).ne'
  simp only [Pi.div_apply]
  rw [levinsonErr_succ_eq_mul hE.ne', show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
  field_simp

/-- **On every nonnegative window**: for a nonzero smooth bump `φ` on `[−a, a]` the lattice
reflection coefficients satisfy `γ_n(φ, h) → (−1)^n` and `(1 − γ_n²)/h² → e_{n+1}/e_n > 0`. -/
theorem reflCoeff_continuumLimit_of_window_nonneg {a : ℝ}
    (hnn : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → 0 ≤ weilQuad G)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφ0 : φ ≠ 0) (n : ℕ) :
    Tendsto (fun h => reflCoeff (weilSeq φ h) n) (𝓝[>] 0) (𝓝 ((-1) ^ n)) ∧
      0 < ((jetGram φ (n + 2)).det / (jetGram φ (n + 1)).det) /
        ((jetGram φ (n + 1)).det / (jetGram φ n).det) ∧
      Tendsto (fun h => (1 - reflCoeff (weilSeq φ h) n ^ 2) / h ^ 2) (𝓝[>] 0)
        (𝓝 (((jetGram φ (n + 2)).det / (jetGram φ (n + 1)).det) /
          ((jetGram φ (n + 1)).det / (jetGram φ n).det))) := by
  have hpd : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → SupportedIn a F → F ≠ 0 → 0 < weilQuad F :=
    fun F hF hFa hF0 => weilQuad_pos_of_window_nonneg hnn hF hFa hF0
  have hJ : ∀ k ≤ n + 2, (jetGram φ k).PosDef := fun k _ => jetGram_posDef hpd hφ hφa hφ0 k
  have hφc := hasCompactSupport_of_supportedIn' hφa
  exact ⟨tendsto_reflCoeff_neg_one_pow hφ hφc n hJ,
    div_pos (div_pos (hJ (n + 2) le_rfl).det_pos (hJ (n + 1) (by omega)).det_pos)
      (div_pos (hJ (n + 1) (by omega)).det_pos (hJ n (by omega)).det_pos),
    tendsto_one_sub_reflCoeff_sq_div_sq hφ hφc n hJ⟩

/-- **Unconditionally on the base window** `2a ≤ 181/250`. -/
theorem reflCoeff_continuumLimit_of_base {a : ℝ} (ha : 2 * a ≤ 181 / 250)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφ0 : φ ≠ 0) (n : ℕ) :
    Tendsto (fun h => reflCoeff (weilSeq φ h) n) (𝓝[>] 0) (𝓝 ((-1) ^ n)) ∧
      Tendsto (fun h => (1 - reflCoeff (weilSeq φ h) n ^ 2) / h ^ 2) (𝓝[>] 0)
        (𝓝 (((jetGram φ (n + 2)).det / (jetGram φ (n + 1)).det) /
          ((jetGram φ (n + 1)).det / (jetGram φ n).det))) := by
  have hpd := fun F (hF : ContDiff ℝ ∞ F) (hFa : SupportedIn a F) (hF0 : F ≠ 0) =>
    weilQuad_pos_of_base ha hF hFa hF0
  have hJ : ∀ k ≤ n + 2, (jetGram φ k).PosDef := fun k _ => jetGram_posDef hpd hφ hφa hφ0 k
  have hφc := hasCompactSupport_of_supportedIn' hφa
  exact ⟨tendsto_reflCoeff_neg_one_pow hφ hφc n hJ, tendsto_one_sub_reflCoeff_sq_div_sq hφ hφc n hJ⟩

end GaloisForLFunctions.SignedWindowCriticality

end

