/-
# The regularized determinant is compact-open continuous in the Schatten norm

The uniform estimate for a power-trace sequence applies verbatim to an operator once the geometric
bound and the convergence of the power traces are supplied by the Schatten norm.  The order-`p`
determinant of a Schatten-converging family therefore converges uniformly on every disc strictly
inside the reciprocal rate, hence locally uniformly on the whole disc of convergence -- the
compact-open topology in which the determinant-completion law is stated.

Main results:
* `tendstoUniformlyOn_opSchattenDet` — **uniform convergence on closed discs**.
* `tendstoLocallyUniformlyOn_opSchattenDet` — **locally uniform convergence on the open disc**.
* `tendstoLocallyUniformlyOn_mul_continuous_right` — a continuous factor preserves uniformity.
* `exists_finiteRank_tendstoLocallyUniformlyOn_opSchattenDet_one` — **the sufficiency half of
  `(DC)` in the compact-open topology**.
-/
import GaloisForLFunctions.HTGeometry.TracePowerDetUniform
import GaloisForLFunctions.HTGeometry.DeterminantGraphLocallyUniform

open Filter Topology Metric ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Uniform convergence of the order-`p` determinant on closed discs.** -/
theorem tendstoUniformlyOn_opSchattenDet {p : ℕ} (hp : 0 < p) {A : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass (p : ℝ) (A n)) (hT : MemSchattenClass (p : ℝ) T)
    (hD : ∀ n, MemSchattenClass (p : ℝ) (A n - T))
    {C : ℝ} (hC1 : 1 ≤ C) (hCA : ∀ n, schattenNorm (p : ℝ) (A n) ≤ C)
    (hCT : schattenNorm (p : ℝ) T ≤ C)
    (htend : Tendsto (fun n => schattenNorm (p : ℝ) (A n - T)) atTop (nhds 0))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρB : ρ * (2 * C) < 1) :
    TendstoUniformlyOn (fun n z => opSchattenDet p (A n) z)
      (fun z => opSchattenDet p T z) atTop (closedBall (0 : ℂ) ρ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hB1 : (1 : ℝ) ≤ 2 * C := by linarith
  have hbound : ∀ (n : ℕ) (k : ℕ), ‖(fun m => opTrace ((A n) ^ m)) (k + p)‖
      ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun n k => norm_opTrace_pow_add_le hp (hA n) hC1 (hCA n) k
  have hboundσ : ∀ k : ℕ, ‖(fun m => opTrace (T ^ m)) (k + p)‖
      ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun k => norm_opTrace_pow_add_le hp hT hC1 hCT k
  have hconv : ∀ k : ℕ, Tendsto (fun n => (fun m => opTrace ((A n) ^ m)) (k + p)) atTop
      (nhds ((fun m => opTrace (T ^ m)) (k + p))) := by
    intro k
    refine tendsto_opTrace_pow_of_tendsto_schattenNorm hpR hA hT hD hCA htend
      (k := k + p) (by omega) ?_
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact tendstoUniformlyOn_tracePowerDet hp hB1 hbound hboundσ hconv hρ0 hρB

/-- **Locally uniform convergence of the order-`p` determinant on the open disc.** -/
theorem tendstoLocallyUniformlyOn_opSchattenDet {p : ℕ} (hp : 0 < p) {A : ℕ → H →L[ℂ] H}
    {T : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass (p : ℝ) (A n)) (hT : MemSchattenClass (p : ℝ) T)
    (hD : ∀ n, MemSchattenClass (p : ℝ) (A n - T))
    {C : ℝ} (hC1 : 1 ≤ C) (hCA : ∀ n, schattenNorm (p : ℝ) (A n) ≤ C)
    (hCT : schattenNorm (p : ℝ) T ≤ C)
    (htend : Tendsto (fun n => schattenNorm (p : ℝ) (A n - T)) atTop (nhds 0))
    {r : ℝ} (hrB : r * (2 * C) < 1) :
    TendstoLocallyUniformlyOn (fun n z => opSchattenDet p (A n) z)
      (fun z => opSchattenDet p T z) atTop (ball (0 : ℂ) r) := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  intro u hu x hx
  have hxr : ‖x‖ < r := by simpa using mem_ball_zero_iff.mp hx
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (‖x‖ + r) / 2 := ⟨_, rfl⟩
  have hxρ : ‖x‖ < ρ := by rw [hρdef]; linarith
  have hρr : ρ < r := by rw [hρdef]; linarith
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg x) hxρ.le
  have hρB : ρ * (2 * C) < 1 := by nlinarith
  have hsub : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := ball_subset_ball hρr.le
  refine ⟨ball (0 : ℂ) ρ, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by simpa using hxρ)))
  · exact ((tendstoUniformlyOn_opSchattenDet hp hA hT hD hC1 hCA hCT htend hρ0 hρB).mono
      ball_subset_closedBall) u hu

/-- Multiplying by a continuous factor preserves locally uniform convergence. -/
theorem tendstoLocallyUniformlyOn_mul_continuous_right {L : Type*} {l : Filter L}
    {g : L → ℂ → ℂ} {g₀ h : ℂ → ℂ} {s : Set ℂ} (hh : Continuous h)
    (hg : TendstoLocallyUniformlyOn g g₀ l s) :
    TendstoLocallyUniformlyOn (fun a z => g a z * h z) (fun z => g₀ z * h z) l s := by
  rw [tendstoLocallyUniformlyOn_iff] at hg ⊢
  intro ε hε x hx
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall x 1).exists_bound_of_continuousOn hh.continuousOn
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg (h x)) (hM x (mem_closedBall_self zero_le_one))
  obtain ⟨t, ht, htu⟩ := hg (ε / (M + 1)) (by positivity) x hx
  refine ⟨t ∩ ball x 1, Filter.inter_mem ht
    (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x one_pos)), ?_⟩
  filter_upwards [htu] with a ha y hy
  obtain ⟨hyt, hyb⟩ := hy
  have h1 : ‖g₀ y - g a y‖ < ε / (M + 1) := by
    have := ha y hyt
    rwa [dist_eq_norm] at this
  have h2 : ‖h y‖ ≤ M := hM y (ball_subset_closedBall hyb)
  rw [dist_eq_norm, ← sub_mul, norm_mul]
  calc ‖g₀ y - g a y‖ * ‖h y‖ ≤ (ε / (M + 1)) * M :=
        mul_le_mul h1.le h2 (norm_nonneg _) (by positivity)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- **The sufficiency half of `(DC)` in the compact-open topology.**  For every Schatten-`p`
operator on an infinite-dimensional Hilbert space and every jet of degree below `p` with vanishing
constant term there are finite-rank operators converging to it in the Schatten norm whose plain
determinants converge *locally uniformly* on a disc about the origin to `exp(Q)` times its
order-`p` regularized determinant. -/
theorem exists_finiteRank_tendstoLocallyUniformlyOn_opSchattenDet_one
    (hH : ¬ FiniteDimensional ℂ H) {p : ℕ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass (p : ℝ) T)
    {Q : Polynomial ℂ} (hdeg : Q.natDegree ≤ p - 1) (hQ0 : Q.coeff 0 = 0) :
    ∃ (F : ℕ → H →L[ℂ] H) (r : ℝ), 0 < r ∧
      (∀ n, ∃ N : ℕ, HasRankLE (F n) N) ∧
      Tendsto (fun n => schattenNorm (p : ℝ) (F n - T)) atTop (nhds 0) ∧
      TendstoLocallyUniformlyOn (fun n z => opSchattenDet 1 (F n) z)
        (fun z => opSchattenDet p T z * Complex.exp (Polynomial.eval z Q)) atTop
        (ball (0 : ℂ) r) := by
  obtain ⟨F, C, hC1, hFrank, hFmem, hCA, hCT, hDtend, hshift, -⟩ :=
    exists_finiteRank_tendsto_opSchattenDet_one hH hp hT hdeg hQ0
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = 1 / (4 * C) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrB : r * (2 * C) < 1 := by
    rw [hrdef, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  have hDmem : ∀ n, MemSchattenClass (p : ℝ) (F n - T) := by
    intro n
    rw [sub_eq_add_neg]
    exact memSchattenClass_add hpR (hFmem n) (memSchattenClass_neg hT)
  have hlu : TendstoLocallyUniformlyOn (fun n z => opSchattenDet p (F n) z)
      (fun z => opSchattenDet p T z) atTop (ball (0 : ℂ) r) :=
    tendstoLocallyUniformlyOn_opSchattenDet hp hFmem hT hDmem hC1 hCA hCT hDtend hrB
  have hmul := tendstoLocallyUniformlyOn_mul_continuous_right
    (h := fun z : ℂ => Complex.exp (Polynomial.eval z Q))
    (Complex.continuous_exp.comp (Polynomial.continuous Q)) hlu
  refine ⟨F, r, hr0, hFrank, hDtend, hmul.congr fun n z hz => ?_⟩
  have hzsmall : ‖z‖ * (2 * C) < 1 := by
    have hzr : ‖z‖ < r := by simpa using mem_ball_zero_iff.mp hz
    have : ‖z‖ * (2 * C) < r * (2 * C) := mul_lt_mul_of_pos_right hzr (by linarith)
    linarith
  exact (hshift n z hzsmall).symm

end

end GaloisForLFunctions.HTGeometry
