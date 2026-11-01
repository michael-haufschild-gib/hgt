import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRoughWirsingBoundIsUniform
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation

/-!
# The multiscale projection bound

On the integer horizon `[1, N]` (Euclidean coordinates `u_n`, pole gauge `y_n = √n u_n`) let `V_Q` be
the space of vectors whose pole gauge depends only on the `Q`-smooth part of `n`
(`smoothFibreSpace`), with orthogonal projection `P_Q`. The spaces increase with `Q`.

* **Rough Poincaré** (`exists_norm_sub_starProjection_sq_le`): `|u − P_Q u|² ≤ (K/log Q) D_N(u)`,
  with `D_N` the pole defect: `P_Q u` is at least as close as the fibre means, whose distance is the
  sum of the rough fibre variances (`sum_fibreVar_le`).
* **Projected mass** (`inner_sq_le_of_mem_smoothFibreSpace`): for `z_n = h(n)/√n` and `v ∈ V_Q`,
  `⟨z, v⟩² ≤ |v|² Σ_a F_a²/(a F_Q(N/a))` with `F_a = Σ_{b ∈ R(Q, N/a)} h(ab)/b`; for a flip twin
  `F_a = ±S_Q(N/a)` and the uniform rough Wirsing bound gives
  `|P_Q ω⃗|² ≤ K' (log N/log Q)^{1−4κ} log Q` (`exists_norm_starProjection_twin_sq_le`).
* **Telescoping** (`abs_inner_sub_starProjection_le`): for nested projections
  `|⟨w, ω − P_0 ω⟩| ≤ Σ_{j<J} |P_{j+1} ω| |w − P_j w| + |ω| |w − P_J w|`.

With scales `Q_j = T^{2^j}` up to `Q_J > √N` these combine into the **multiscale bound**
(`exists_abs_inner_twin_sub_starProjection_le`): for `κ < 1/4`,
`|⟨u, ω⃗ − P_T ω⃗⟩| ≤ (K₁ (log N)^{1/2 − 2κ} (log T)^{2κ − 1/2} + K₂) √D_N(u)`: the rough
fluctuations of the twin have Dirichlet dual norm `≪ (log T)^{2κ−1/2} c_N √H_N`.
-/

open Finset Filter Topology
open scoped RealInnerProductSpace
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (gaugeHarmonicSum horizonExtend
  horizonExtend_coe sum_horizonExtend)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (roughInterval roughHarmonic smoothSet
  mem_smoothSet mem_roughInterval sum_Icc_eq_smooth_rough PrimeHorizonIndex poleDefect poleGauge
  fibreMean harmonicVar wVar wMean walkEnergy sum_fibreVar_le exists_harmonicVar_le_glauberForm_rough
  walkEnergy_small_add_large walkEnergy_nonneg one_le_roughHarmonic)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

section SmoothPart

/-- The `Q`-smooth part of `n`: the product of its prime powers `p^k` with `p < Q`. -/
def smoothPart (Q n : ℕ) : ℕ := (n.factorization.filter (· < Q)).prod fun p k => p ^ k

theorem factorization_smoothPart (Q n : ℕ) :
    (smoothPart Q n).factorization = n.factorization.filter (· < Q) := by
  refine Nat.prod_pow_factorization_eq_self fun p hp => ?_
  rw [Finsupp.support_filter, mem_filter, Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

theorem smoothPart_ne_zero (Q n : ℕ) : smoothPart Q n ≠ 0 := by
  unfold smoothPart Finsupp.prod
  refine prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
  rw [Finsupp.support_filter, mem_filter, Nat.support_factorization] at hp
  exact (Nat.prime_of_mem_primeFactors hp.1).ne_zero

/-- Smooth parts are compatible: `sp_Q (sp_{Q'} n) = sp_Q n` for `Q ≤ Q'`. -/
theorem smoothPart_smoothPart {Q Q' : ℕ} (h : Q ≤ Q') (n : ℕ) :
    smoothPart Q (smoothPart Q' n) = smoothPart Q n := by
  refine Nat.eq_of_factorization_eq (smoothPart_ne_zero _ _) (smoothPart_ne_zero _ _) fun p => ?_
  rw [factorization_smoothPart, factorization_smoothPart, factorization_smoothPart]
  simp only [Finsupp.filter_apply]
  split_ifs <;> omega

/-- The smooth part of `a b` with `a` `Q`-smooth and `b` `Q`-rough is `a`. -/
theorem smoothPart_mul {Q a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : ∀ p ∈ a.primeFactors, p < Q) (hb : ∀ p ∈ b.primeFactors, Q ≤ p) :
    smoothPart Q (a * b) = a := by
  refine Nat.eq_of_factorization_eq (smoothPart_ne_zero _ _) ha0 fun p => ?_
  rw [factorization_smoothPart, Nat.factorization_mul ha0 hb0, Finsupp.filter_apply,
    Finsupp.add_apply]
  by_cases hp : p < Q
  · rw [if_pos hp]
    have : b.factorization p = 0 := by
      by_contra h
      have := hb p (by rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h)
      omega
    omega
  · rw [if_neg hp]
    have : a.factorization p = 0 := by
      by_contra h
      exact hp (ha p (by rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h))
    omega

end SmoothPart

section Subspaces

variable {N : ℕ}

/-- The vectors whose pole gauge `√n u_n` depends only on the `Q`-smooth part of `n`. -/
def smoothFibreSpace (Q N : ℕ) : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) where
  carrier := {u | ∀ i j : PrimeHorizonIndex N, smoothPart Q i = smoothPart Q j →
    Real.sqrt i * u i = Real.sqrt j * u j}
  add_mem' {u v} hu hv i j h := by
    simp only [PiLp.add_apply, mul_add, hu i j h, hv i j h]
  zero_mem' i j _ := by simp
  smul_mem' c u hu i j h := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [mul_left_comm, hu i j h, mul_left_comm]

theorem smoothFibreSpace_mono {Q Q' : ℕ} (h : Q ≤ Q') :
    smoothFibreSpace Q N ≤ smoothFibreSpace Q' N := fun _ hu i j hij =>
  hu i j (by rw [← smoothPart_smoothPart h i, hij, smoothPart_smoothPart h j])

theorem real_inner_eq_sum (u v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪u, v⟫ = ∑ i, u i * v i := by
  simp [PiLp.inner_apply, mul_comm]

/-- The vector `(h(n)/√n)_{n ≤ N}`. -/
def gaugeVector (N : ℕ) (h : ℕ → ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 fun i => h i / Real.sqrt i

/-- The fibration of `[1, N]` over `Q`-smooth parts, in pole gauge: for `v ∈ V_Q` the pole gauge
`g(n) = √n v_n` is constant on each fibre `a · R(Q, N/a)`. -/
theorem poleGauge_mul_of_mem {Q : ℕ} {v : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hv : v ∈ smoothFibreSpace Q N) {a b : ℕ} (ha : a ∈ smoothSet Q N)
    (hb : b ∈ roughInterval Q (N / a)) :
    Real.sqrt ((a * b : ℕ) : ℝ) * horizonExtend v (a * b) = Real.sqrt a * horizonExtend v a := by
  obtain ⟨ha1, haN, hap⟩ := mem_smoothSet.mp ha
  obtain ⟨hb1, hbN, hbp⟩ := mem_roughInterval.mp hb
  have habN : a * b ≤ N := by
    have := Nat.mul_le_mul_left a hbN
    exact this.trans (Nat.mul_div_le N a)
  have hab : a * b ∈ Icc 1 N := mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), habN⟩
  have ha' : a ∈ Icc 1 N := mem_Icc.mpr ⟨ha1, haN⟩
  have hsp : smoothPart Q (a * b) = smoothPart Q a := by
    rw [smoothPart_mul (by omega) (by omega) hap (fun p hp => hbp p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)),
      ← mul_one a, smoothPart_mul (by omega) one_ne_zero hap (by simp), mul_one]
  have := hv ⟨a * b, hab⟩ ⟨a, ha'⟩ hsp
  simp only [horizonExtend, dif_pos hab, dif_pos ha']
  exact this

end Subspaces

section Projections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The projection is at least as close as any point of the subspace. -/
theorem norm_sub_starProjection_le {U : Submodule ℝ E} [U.HasOrthogonalProjection] (y : E)
    {x : E} (hx : x ∈ U) : ‖y - U.starProjection y‖ ≤ ‖y - x‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ ⟨x, hx⟩

/-- `|⟨w, z − P z⟩| ≤ |w − P w| |z|`. -/
theorem abs_inner_sub_starProjection_le_one {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (w z : E) : |⟪w, z - U.starProjection z⟫| ≤ ‖w - U.starProjection w‖ * ‖z‖ := by
  have h0 : ⟪U.starProjection w, z - U.starProjection z⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero z _ (U.starProjection_apply_mem w)
  have e : ⟪w, z - U.starProjection z⟫ = ⟪w - U.starProjection w, z - U.starProjection z⟫ := by
    rw [inner_sub_left, h0, sub_zero]
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  simpa using norm_sub_starProjection_le z (zero_mem U)

/-- **Projected mass from a test bound**: if `⟨z, v⟩² ≤ M |v|²` on `U` (`M ≥ 0`), then `|P z|² ≤ M`. -/
theorem norm_starProjection_sq_le {U : Submodule ℝ E} [U.HasOrthogonalProjection] (z : E)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ v ∈ U, ⟪z, v⟫ ^ 2 ≤ M * ‖v‖ ^ 2) :
    ‖U.starProjection z‖ ^ 2 ≤ M := by
  set p := U.starProjection z
  have hp : ⟪z, p⟫ = ‖p‖ ^ 2 := by
    have h0 : ⟪z - p, p⟫ = 0 := Submodule.starProjection_inner_eq_zero z p (U.starProjection_apply_mem z)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h0; linarith
  have h := hM p (U.starProjection_apply_mem z)
  rw [hp] at h
  rcases (sq_nonneg ‖p‖).eq_or_lt with h' | h'
  · rw [← h']; exact hM0
  · nlinarith

/-- **Telescoping over nested projections.** For `K 0 ≤ K 1 ≤ ⋯`,
`|⟨w, ω − P_0 ω⟩| ≤ Σ_{j<J} |P_{j+1} ω| |w − P_j w| + |ω| |w − P_J w|`: each increment
`P_{j+1} ω − P_j ω = z − P_j z` with `z = P_{j+1} ω` is orthogonal to `K j`. -/
theorem abs_inner_sub_starProjection_le (K : ℕ → Submodule ℝ E)
    [∀ j, (K j).HasOrthogonalProjection] (hK : ∀ j, K j ≤ K (j + 1)) (ω w : E) (J : ℕ) :
    |⟪w, ω - (K 0).starProjection ω⟫| ≤
      ∑ j ∈ range J, ‖(K (j + 1)).starProjection ω‖ * ‖w - (K j).starProjection w‖ +
        ‖ω‖ * ‖w - (K J).starProjection w‖ := by
  have htel : ⟪w, ω - (K 0).starProjection ω⟫ =
      ∑ j ∈ range J, ⟪w, (K (j + 1)).starProjection ω - (K j).starProjection ω⟫ +
        ⟪w, ω - (K J).starProjection ω⟫ := by
    rw [← inner_sum, ← inner_add_right, sum_range_sub (fun j => (K j).starProjection ω)]
    congr 1; abel
  have hstep : ∀ j, |⟪w, (K (j + 1)).starProjection ω - (K j).starProjection ω⟫| ≤
      ‖(K (j + 1)).starProjection ω‖ * ‖w - (K j).starProjection w‖ := by
    intro j
    have hcomp : (K j).starProjection ((K (j + 1)).starProjection ω) = (K j).starProjection ω :=
      congrArg (fun f => f ω) (Submodule.starProjection_comp_starProjection_of_le (hK j))
    have h := abs_inner_sub_starProjection_le_one (U := K j) w ((K (j + 1)).starProjection ω)
    rw [hcomp] at h
    rw [mul_comm]; exact h
  have hlast := abs_inner_sub_starProjection_le_one (U := K J) w ω
  rw [htel]
  refine (abs_add_le _ _).trans (add_le_add ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun j _ => hstep j)) ?_)
  rw [mul_comm]; exact hlast

end Projections

end GaloisForLFunctions.RenormalizedIntersectionTheory
