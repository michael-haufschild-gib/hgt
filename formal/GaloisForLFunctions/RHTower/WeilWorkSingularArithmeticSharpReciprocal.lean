import GaloisForLFunctions.RHTower.WeilProducerMobiusCancellation
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletLSeriesBridge
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel

/-!
# Sharp half-power cancellation for producer reciprocal coefficients

Every full-cone Weil-positive system has ordinary reciprocal-coefficient sums
of size `O(N^(1/2+ε))`, for each `ε > 0`. A smooth cutoff of width `1/2`
agrees exactly with the sharp cutoff on integers. Fractional Mellin decay
and subpolynomial growth of the literal reciprocal pay the narrowing cost.
No bound on the individual reciprocal coefficients is required.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- Smoothing inside one integer gap leaves every arithmetic sum unchanged. -/
theorem tsum_halfWidth_eq_sum (b : ℕ → ℂ) (N : ℕ) :
    (∑' n : ℕ, b n * ((smoothWeight N (1 / 2) n : ℝ) : ℂ)) =
      ∑ n ∈ Finset.range (N + 1), b n := by
  classical
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [smoothWeight_eq_one (by norm_num) hnN, Complex.ofReal_one, mul_one]
  · intro n hn
    have hNn : N + 1 ≤ n := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
    have hNn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hNn
    rw [smoothWeight_eq_zero (by norm_num) (by linarith), Complex.ofReal_zero, mul_zero]

/-- All vertical twists of the actual reciprocal sums have half-power
cancellation, with arbitrarily small polynomial height loss and no exceptional set. -/
theorem exists_sharp_twisted_reciprocal_sum_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (t : ℝ),
      ‖∑ n ∈ Finset.range (N + 1),
        producerMobius (fun n => if 2 ≤ n then lam n else 0) n * (n : ℂ) ^ (-(t : ℂ) * I)‖ ≤
          C * ((N : ℝ) + 1) ^ (1 / 2 + ε) * (2 + |t|) ^ ε := by
  let lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have h1 : lam' 1 = 0 := by simp [lam']
  have hA : DifferentiableOn ℂ zetaArchimedeanDatum
      {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  obtain ⟨G, hGd, hGL⟩ := exists_reciprocalZeta_continuation hH h1 hA
  let q : ℝ := min (ε / 4) (1 / 4)
  let a : ℝ := q / 2
  let c : ℝ := 1 / 2 + q
  have hq : 0 < q := by dsimp [q]; positivity
  have hq4 : q ≤ 1 / 4 := min_le_right _ _
  have hqε : q ≤ ε / 4 := min_le_left _ _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haq : a < q := by dsimp [a]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by dsimp [c]; linarith
  have hcr : c + q ≤ 1 / 2 + ε := by dsimp [c]; linarith
  obtain ⟨Kb, hKb, hbd⟩ := exists_reciprocalZeta_strip_bound hH h1 hK hA hAK hq
    (by linarith : q < 1 / 2) (ε := a) (by dsimp [a]; positivity) hGd hGL
  obtain ⟨C₀, C₁, hC₀, hC₁, hfrac⟩ :=
    exists_integral_norm_mul_mellin_smoothWeight_fractional_bound
  let P : ℝ := C₀ ^ (1 - q) * C₁ ^ q
  let B : ℝ := 2 * (Kb * 3 ^ a) / c +
    2 * (Kb * 3 ^ a) * P * 2 ^ q / (q - a)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  refine ⟨B / (2 * Real.pi), div_nonneg hB hpi.le, fun N t => ?_⟩
  rcases N.eq_zero_or_pos with rfl | hN
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, producerMobius_zero,
      zero_mul, add_zero, norm_zero]
    positivity
  let b : ℕ → ℂ := fun n => producerMobius lam' n * (n : ℂ) ^ (-(t : ℂ) * I)
  let Gt : ℂ → ℂ := fun s => G (s + (t : ℂ) * I)
  let Kt : ℝ := Kb * (2 + |t|) ^ a
  have hKt : 0 ≤ Kt := by dsimp [Kt]; positivity
  have hGtd : DifferentiableOn ℂ Gt {s : ℂ | 1 / 2 < s.re} :=
    hGd.comp (differentiable_id.add_const ((t : ℂ) * I)).differentiableOn
      fun s hs => by simpa using hs
  have hbdt : ∀ s ∈ verticalStrip c 2, ‖Gt s‖ ≤ Kt * (2 + |s.im|) ^ a := by
    intro s hs
    have hmem : s + (t : ℂ) * I ∈ verticalStrip (1 / 2 + q) 2 := by
      simpa [verticalStrip, c] using hs
    have habs : 2 + |s.im + t| ≤ (2 + |s.im|) * (2 + |t|) := by
      have := abs_add_le s.im t
      have := abs_nonneg s.im
      have := abs_nonneg t
      nlinarith
    calc ‖Gt s‖ ≤ Kb * (2 + |s.im + t|) ^ a := by simpa [Gt] using hbd _ hmem
      _ ≤ Kb * ((2 + |s.im|) * (2 + |t|)) ^ a :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) habs ha) hKb
      _ = Kt * (2 + |s.im|) ^ a := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        dsimp [Kt]
        ring
  have htwist : ∀ n : ℕ, n ≠ 0 → ‖(n : ℂ) ^ (-(t : ℂ) * I)‖ = 1 := by
    intro n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have := Complex.norm_cpow_eq_rpow_re_of_pos hn0 (-(t : ℂ) * I)
    simpa using this
  have hb0 : b 0 = 0 := by simp [b, producerMobius_zero]
  have hsum : Summable (fun n : ℕ => ‖b n‖ * (n : ℝ) ^ (-(2 : ℝ))) := by
    apply (summable_norm_producerMobius_mul_rpow hH.summable).congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [b, producerMobius_zero]
    · simp only [b, lam', norm_mul, htwist n hn, mul_one]
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ (N : ℝ) + 1 := by linarith
  have hstrip : verticalStrip c 2 ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    show 1 / 2 < s.re
    have := hs.1
    dsimp [c] at this
    linarith
  have hperron := Sieve.tsum_mul_smoothWeight_eq_integral_summable
    hb0 hN0 (by norm_num : (0 : ℝ) < 1 / 2) (σ := 2) (by norm_num) hsum
  have heq : (fun y : ℝ => (∑' n : ℕ, b n *
      (n : ℂ) ^ (-((2 : ℂ) + y * I))) *
        mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ)) (2 + y * I)) =
      fun y : ℝ => Gt (2 + y * I) *
        mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ)) (2 + y * I) := by
    funext y
    have hre : 1 < ((2 : ℂ) + y * I + (t : ℂ) * I).re := by simp
    have hterms : (fun n : ℕ => b n * (n : ℂ) ^ (-((2 : ℂ) + y * I))) =
        fun n : ℕ => producerMobius lam' n *
          (n : ℂ) ^ (-((2 : ℂ) + y * I + (t : ℂ) * I)) := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [b, producerMobius_zero]
      · have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
        dsimp [b]
        rw [mul_assoc, ← Complex.cpow_add _ _ hnc]
        congr 2
        ring
    rw [hterms, tsum_producerMobius_mul_cpow_eq hH.summable hre]
    exact congrArg (fun z : ℂ => z * _) (hGL _ hre).symm
  norm_num only [Complex.ofReal_ofNat] at hperron
  rw [heq] at hperron
  have hshift := integral_mul_mellin_smoothWeight_shift hN0
    (by norm_num : (0 : ℝ) < 1 / 2) hc hc2 (hGtd.mono hstrip) hKt ha hbdt
  norm_num only [Complex.ofReal_ofNat] at hshift
  rw [hshift] at hperron
  have hline : ∀ y : ℝ, ‖Gt ((c : ℂ) + y * I)‖ ≤ Kt * (2 + |y|) ^ a := by
    intro y
    simpa using hbdt ((c : ℂ) + y * I) ⟨by simp, by simp; exact hc2⟩
  have hint := integrable_mul_mellin_smoothWeight_line hN0 (by norm_num : (0 : ℝ) < 1 / 2)
    hc (hGtd.mono hstrip).continuousOn hKt ha hbdt le_rfl hc2
  have hbound := hfrac N (1 / 2) c a q Kt hN0 (by norm_num) hc ha haq
    (by linarith : q ≤ 1) hKt Gt hline hint
  have hX : ((N : ℝ) + 1 / 2) ^ c ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    exact (Real.rpow_le_rpow (by positivity) (by linarith) hc.le).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hRX : (((N : ℝ) + 1 / 2) / (1 / 2)) ^ q * ((N : ℝ) + 1 / 2) ^ c ≤
      2 ^ q * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
    calc
      _ ≤ (2 * ((N : ℝ) + 1)) ^ q * ((N : ℝ) + 1) ^ c :=
        mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) hq.le)
          (Real.rpow_le_rpow (by positivity) (by linarith) hc.le)
          (by positivity) (by positivity)
      _ = 2 ^ q * ((N : ℝ) + 1) ^ (c + q) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), mul_assoc,
          ← Real.rpow_add (by positivity), add_comm q c]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 hcr) (by positivity)
  have hmain := mul_le_mul_of_nonneg_left hX
    (show 0 ≤ 2 * (Kt * 3 ^ a) / c by positivity)
  have htail := mul_le_mul_of_nonneg_left hRX
    (show 0 ≤ 2 * (Kt * 3 ^ a) * P / (q - a) by positivity)
  have hmass : (∫ y : ℝ, ‖Gt ((c : ℂ) + y * I) *
      mellin (fun x : ℝ => ((smoothWeight N (1 / 2) x : ℝ) : ℂ)) ((c : ℂ) + y * I)‖) ≤
        B * ((N : ℝ) + 1) ^ (1 / 2 + ε) * (2 + |t|) ^ a := by
    refine hbound.trans ?_
    convert add_le_add hmain htail using 1 <;> dsimp [B, P, Kt] <;> ring
  have hnorm : (2 * Real.pi) * ‖∑ n ∈ Finset.range (N + 1), b n‖ ≤
      B * ((N : ℝ) + 1) ^ (1 / 2 + ε) * (2 + |t|) ^ a := by
    rw [← tsum_halfWidth_eq_sum, ← abs_of_pos hpi, ← Real.norm_eq_abs, ← norm_smul, hperron]
    exact (norm_integral_le_integral_norm _).trans hmass
  have hheight : (2 + |t|) ^ a ≤ (2 + |t|) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le (by have := abs_nonneg t; linarith)
      (by dsimp [a]; linarith)
  change ‖∑ n ∈ Finset.range (N + 1), b n‖ ≤ _
  calc
    _ ≤ B / (2 * Real.pi) * ((N : ℝ) + 1) ^ (1 / 2 + ε) * (2 + |t|) ^ a := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hpi]
      simpa only [mul_comm] using hnorm
    _ ≤ _ := mul_le_mul_of_nonneg_left hheight (by positivity)

/-- The untwisted specialization needs no coefficient regularity premise. -/
theorem exists_sharp_reciprocal_sum_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Finset.range (N + 1),
        producerMobius (fun n => if 2 ≤ n then lam n else 0) n‖ ≤
          C * ((N : ℝ) + 1) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_sharp_twisted_reciprocal_sum_le hW hε
  refine ⟨C * 2 ^ ε, by positivity, fun N => ?_⟩
  simpa only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one,
    abs_zero, add_zero, mul_right_comm] using hbound N 0

/-- The ordinary reciprocal series converges everywhere in the full critical
half-plane. Its convergence requires no separate coefficient hypothesis. -/
theorem reciprocal_dirichletConvergesAt {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DirichletConvergesAt
      (fun n => producerMobius (fun n => if 2 ≤ n then lam n else 0) (n + 1)) s := by
  let ε : ℝ := (s.re - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_sharp_reciprocal_sum_le hW hε
  apply tendsto_dirichlet_partialSum_of_poly_bounded hC
    (show 0 ≤ 1 / 2 + ε by linarith) _ (show 1 / 2 + ε < s.re by dsimp [ε]; linarith)
  intro N
  simpa only [Finset.sum_range_succ', producerMobius_zero, add_zero] using hbound N

/-- The same literal reciprocal is the ordinary sum on `Re s > 1/2`, and its
ordinary harmonic series sums to zero. Every analytic and arithmetic premise
is supplied by full-cone Weil positivity. -/
theorem exists_ordinary_reciprocal {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      G 1 = 0 ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
          LSeries.term (producerMobius (fun n => if 2 ≤ n then lam n else 0)) s n)
          atTop (𝓝 (G s)) := by
  let lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  let b : ℕ → ℂ := fun n => producerMobius lam' (n + 1)
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have hA : DifferentiableOn ℂ zetaArchimedeanDatum U :=
    differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith
  obtain ⟨Φ, hΦd, -, hΦid⟩ := hH.herglotz
  obtain ⟨c, P, -, hPd, hGL⟩ := exists_reciprocalZeta_primitive hH
    (by simp [lam'] : lam' 1 = 0) hA hΦd hΦid
  let G : ℂ → ℂ := fun s => c * ((s - 1) * cexp (P s))
  have hGd : DifferentiableOn ℂ G U := fun s hs =>
    ((((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul c).differentiableAt
      |>.differentiableWithinAt
  have hconv : ∀ s ∈ U, DirichletConvergesAt b s :=
    fun _ hs => reciprocal_dirichletConvergesAt hW hs
  have hDd : DifferentiableOn ℂ (dirichletSum b) U := by
    intro s hs
    let s₀ : ℂ := (((1 / 2 + s.re) / 2 : ℝ) : ℂ)
    have hs₀U : s₀ ∈ U := by
      change 1 / 2 < ((1 / 2 + s.re) / 2 : ℝ)
      change 1 / 2 < s.re at hs
      linarith
    have hlt : s₀.re < s.re := by
      change ((1 / 2 + s.re) / 2 : ℝ) < s.re
      change 1 / 2 < s.re at hs
      linarith
    have hopen : IsOpen {z : ℂ | s₀.re < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact ((differentiableOn_dirichletSum (hconv s₀ hs₀U)).differentiableAt
      (hopen.mem_nhds hlt)).differentiableWithinAt
  have hagreeR : ∀ s : ℂ, 1 < s.re → dirichletSum b s = G s := by
    intro s hs
    obtain ⟨hLS, hLeq⟩ := LSeries_producerMobius hH.summable hs
    have hhas : HasSum (fun n => LSeries.term (producerMobius lam') s (n + 1))
        (LSeries (producerMobius lam') s) := by
      have := (hasSum_nat_add_iff' 1).mpr hLS.LSeriesHasSum
      simpa [LSeries.term_zero] using this
    have htend : Tendsto (fun N => dirichletPartialSum b N s) atTop
        (𝓝 (LSeries (producerMobius lam') s)) := by
      refine hhas.tendsto_sum_nat.congr fun N => Finset.sum_congr rfl fun n _ => ?_
      exact term_succ_eq (producerMobius lam') s n
    rw [tendsto_nhds_unique (tendsto_dirichletSum ⟨_, htend⟩) htend, hLeq]
    exact (hGL s hs).symm
  have hagree : EqOn (dirichletSum b) G U := by
    have h2U : (2 : ℂ) ∈ U := by change (1 : ℝ) / 2 < (2 : ℂ).re; norm_num
    refine (hDd.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
      (hGd.analyticOnNhd hUopen) (convex_halfSpace_re_gt (1 / 2)).isPreconnected h2U ?_
    have hV : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hV.mem_nhds (show 1 < (2 : ℂ).re by norm_num)] with z hz
    exact hagreeR z hz
  refine ⟨G, hGd, hGL, by simp [G], fun s hs => ?_⟩
  have htend := tendsto_dirichletSum (hconv s hs)
  rw [hagree hs] at htend
  simpa only [b, dirichletPartialSum_eq_sum_term] using htend

end RHTower.WeilSingularArithmetic
