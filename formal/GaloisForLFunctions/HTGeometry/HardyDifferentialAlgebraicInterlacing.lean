import GaloisForLFunctions.HTGeometry.HardyDiskSpace
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnSum
import GaloisForLFunctions.HTGeometry.MeromorphicMultiplicativeTranslationDefect
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicCompactOpenMeagre
import GaloisForLFunctions.HTGeometry.FixedModulusRealRootednessNonselection

/-!
# Both differential phases are norm dense in the Hardy space of the disk

Polynomials are differentially algebraic and dense in `H²(D)`, so the differentially algebraic
phase is dense.  Conversely, fix one bounded hypertranscendental carrier — the entire reciprocal
Gamma function, whose Taylor coefficients at the origin are square summable.  For every `a` at most
one scalar `λ` can make `a + λ c` differentially algebraic, since a second one would make the
carrier itself differentially algebraic.  Shrinking `λ` therefore approximates every `a` by
hypertranscendental elements.

The Hardy statement of the DA/HT interlacing law: both phases are norm dense, so no norm-continuous
map into a Hausdorff space can separate them.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

/-- The open unit disk as an ambient domain. -/
abbrev unitDiskDomain : Set ℂ := Metric.ball (0 : ℂ) 1

theorem isOpen_unitDiskDomain : IsOpen unitDiskDomain := Metric.isOpen_ball

theorem nonempty_unitDiskDomain : (unitDiskDomain).Nonempty :=
  ⟨0, by simp [unitDiskDomain]⟩

theorem isPreconnected_unitDiskDomain : IsPreconnected unitDiskDomain :=
  (convex_ball (0 : ℂ) 1).isPreconnected

theorem infinite_unitDiskDomain : (unitDiskDomain).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => domainSampleNode (0 : ℂ) 1 k) ?_ ?_
  · exact domainSampleNode_injective 0 one_pos
  · intro k
    simpa [unitDiskDomain] using domainSampleNode_mem_ball (0 : ℂ) one_pos k

theorem mem_unitDiskDomain_iff {z : ℂ} : z ∈ unitDiskDomain ↔ ‖z‖ < 1 := by
  simp [unitDiskDomain, Metric.mem_ball, dist_zero_right]

/-! ## Polynomials are differentially algebraic on any set -/

private theorem iteratedDeriv_polyEval (p : Polynomial ℂ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun x => p.eval x) z = ((⇑Polynomial.derivative)^[j] p).eval z := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ', Function.iterate_succ_apply]
      have hderiv : deriv (fun x : ℂ => p.eval x) = fun x => (Polynomial.derivative p).eval x := by
        funext x
        exact p.deriv
      rw [hderiv, ih]

theorem differentiallyAlgebraicOn_polynomial (U : Set ℂ) (B : Polynomial ℂ) :
    DifferentiallyAlgebraicOn (fun z => B.eval z) U := by
  classical
  set m : ℕ := B.natDegree with hm
  refine ⟨m + 1, MvPolynomial.X ⟨m + 2, by omega⟩, MvPolynomial.X_ne_zero _, ?_⟩
  intro z _
  have hidx : (⟨m + 2, by omega⟩ : Fin (m + 1 + 2))
      = Fin.succ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) := by
    apply Fin.ext
    simp
  rw [MvPolynomial.eval_X, hidx, Fin.cons_succ]
  have hzero : (⇑Polynomial.derivative)^[m + 1] B = 0 :=
    Polynomial.iterate_derivative_eq_zero (by omega)
  simp only []
  rw [iteratedDeriv_polyEval B (m + 1) z, hzero]
  simp

/-! ## Density of the differentially algebraic phase -/

/-- The differentially algebraic phase of the Hardy space. -/
def hardyDALocus : Set HardyDisk :=
  {a | DifferentiallyAlgebraicOn (hardyFun a) unitDiskDomain}

theorem hardyFun_of_finite_support {a : HardyDisk} {N : ℕ}
    (hsupp : ∀ n, N ≤ n → (a : ℕ → ℂ) n = 0) {z : ℂ} (_hz : ‖z‖ < 1) :
    hardyFun a z = ∑ n ∈ Finset.range N, (a : ℕ → ℂ) n * z ^ n := by
  classical
  rw [hardyFun, tsum_eq_sum (s := Finset.range N)]
  intro n hn
  rw [hsupp n (Nat.not_lt.1 (fun hcon => hn (Finset.mem_range.2 hcon))), zero_mul]

theorem dense_hardyDALocus : Dense hardyDALocus := by
  classical
  rw [Metric.dense_iff]
  intro a ε hε
  have hsum := lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) a
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hsum.tendsto_sum_nat ε hε
  set b : HardyDisk := ∑ i ∈ Finset.range N, lp.single 2 i ((a : ℕ → ℂ) i) with hb
  have hcoord : ∀ n, N ≤ n → (b : ℕ → ℂ) n = 0 := by
    intro n hn
    have hcf : (b : ℕ → ℂ) n
        = ∑ i ∈ Finset.range N, ((lp.single 2 i ((a : ℕ → ℂ) i) : HardyDisk) : ℕ → ℂ) n := by
      rw [hb, lp.coeFn_sum]
      simp
    rw [hcf]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [lp.single_apply, Pi.single_apply, if_neg]
    intro hcon
    exact absurd (hcon ▸ Finset.mem_range.1 hi) (Nat.not_lt.2 hn)
  refine ⟨b, ?_, ?_⟩
  · rw [Metric.mem_ball]
    exact hN N le_rfl
  · have hfun : Set.EqOn (hardyFun b)
        (fun z => (∑ n ∈ Finset.range N,
          Polynomial.C ((b : ℕ → ℂ) n) * Polynomial.X ^ n).eval z) unitDiskDomain := by
      intro z hz
      have hL := hardyFun_of_finite_support hcoord (mem_unitDiskDomain_iff.1 hz)
      show hardyFun b z = Polynomial.eval z
        (∑ n ∈ Finset.range N, Polynomial.C ((b : ℕ → ℂ) n) * Polynomial.X ^ n)
      rw [hL, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun n _ => by simp
    exact differentiallyAlgebraicOn_of_eqOn isOpen_unitDiskDomain hfun.symm
      (differentiallyAlgebraicOn_polynomial _ _)


/-! ## A bounded hypertranscendental carrier in the Hardy space -/

theorem analyticOnNhd_reciprocalGammaEntire_univ :
    AnalyticOnNhd ℂ reciprocalGammaEntire (Set.univ : Set ℂ) := by
  simpa using FixedModulusRealRootedness.analyticOnNhd_iteratedDeriv_reciprocalGammaEntire 0

theorem hasFPowerSeriesOnBall_reciprocalGammaEntire :
    HasFPowerSeriesOnBall reciprocalGammaEntire
      (cauchyPowerSeries reciprocalGammaEntire 0 ((2 : NNReal) : ℝ)) 0 ((2 : NNReal) : ENNReal) := by
  refine DifferentiableOn.hasFPowerSeriesOnBall (R := (2 : NNReal)) ?_ (by norm_num)
  exact (analyticOnNhd_reciprocalGammaEntire_univ.mono (Set.subset_univ _)).differentiableOn

theorem summable_norm_diskCoeff_reciprocalGammaEntire :
    Summable (fun n => ‖diskCoeff reciprocalGammaEntire n‖) := by
  set p := cauchyPowerSeries reciprocalGammaEntire 0 ((2 : NNReal) : ℝ) with hp
  have hball := hasFPowerSeriesOnBall_reciprocalGammaEntire
  have hrad : ((2 : NNReal) : ENNReal) ≤ p.radius := by
    simpa [hp] using hball.r_le
  have hlt : ((1 : NNReal) : ENNReal) < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have hs := p.summable_norm_mul_pow (r := (1 : NNReal)) hlt
  simp only [NNReal.coe_one, one_pow, mul_one] at hs
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  rw [← coeff_eq_diskCoeff hball n]
  have hb := (p n).le_opNorm (fun _ : Fin n => (1 : ℂ))
  have hcoeff : p.coeff n = (p n) (fun _ : Fin n => (1 : ℂ)) := rfl
  rw [hcoeff]
  simpa using hb

theorem memℓp_diskCoeff_reciprocalGammaEntire :
    Memℓp (diskCoeff reciprocalGammaEntire) 2 := by
  have hs := summable_norm_diskCoeff_reciprocalGammaEntire
  set B : ℝ := ∑' n, ‖diskCoeff reciprocalGammaEntire n‖ with hB
  have hle : ∀ n, ‖diskCoeff reciprocalGammaEntire n‖ ≤ B := fun n =>
    hs.le_tsum n (fun m _ => norm_nonneg _)
  have hsq : Summable (fun n => ‖diskCoeff reciprocalGammaEntire n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs.mul_left B)
    have h0 : (0:ℝ) ≤ ‖diskCoeff reciprocalGammaEntire n‖ := norm_nonneg _
    nlinarith [hle n, h0]
  rw [memℓp_gen_iff (by norm_num)]
  refine hsq.congr fun n => ?_
  rw [← Real.rpow_natCast ‖diskCoeff reciprocalGammaEntire n‖ 2]
  norm_num

/-- The hypertranscendental Hardy carrier. -/
def hardyHTCarrier : HardyDisk := ⟨diskCoeff reciprocalGammaEntire, memℓp_diskCoeff_reciprocalGammaEntire⟩

theorem hardyFun_hardyHTCarrier_eqOn :
    Set.EqOn (hardyFun hardyHTCarrier) reciprocalGammaEntire unitDiskDomain := by
  intro z hz
  have hball := hasFPowerSeriesOnBall_reciprocalGammaEntire
  have hzlt : ‖z‖ < 2 := lt_trans (mem_unitDiskDomain_iff.1 hz) (by norm_num)
  have hz2 : z ∈ Metric.eball (0 : ℂ) ((2 : NNReal) : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right]
    have hnn : ‖z‖₊ < (2 : NNReal) := by
      rw [← NNReal.coe_lt_coe]
      simpa using hzlt
    calc ‖z‖ₑ = ((‖z‖₊ : NNReal) : ENNReal) := rfl
      _ < ((2 : NNReal) : ENNReal) := by exact_mod_cast hnn
  have hsum := hball.hasSum hz2
  have hterm : ∀ n : ℕ,
      (cauchyPowerSeries reciprocalGammaEntire 0 ((2 : NNReal) : ℝ) n fun _ => z)
        = diskCoeff reciprocalGammaEntire n * z ^ n := by
    intro n
    rw [(cauchyPowerSeries reciprocalGammaEntire 0 ((2 : NNReal) : ℝ)).apply_eq_pow_smul_coeff,
      coeff_eq_diskCoeff hball n, smul_eq_mul, mul_comm]
  have hsum0 : HasSum (fun n =>
      (cauchyPowerSeries reciprocalGammaEntire 0 ((2 : NNReal) : ℝ) n fun _ => z))
      (reciprocalGammaEntire z) := by simpa using hsum
  have hsum' : HasSum (fun n => diskCoeff reciprocalGammaEntire n * z ^ n)
      (reciprocalGammaEntire z) := hsum0.congr_fun (fun n => (hterm n).symm)
  show hardyFun hardyHTCarrier z = reciprocalGammaEntire z
  rw [hardyFun]
  exact hsum'.tsum_eq

theorem not_differentiallyAlgebraicOn_hardyHTCarrier :
    ¬ DifferentiallyAlgebraicOn (hardyFun hardyHTCarrier) unitDiskDomain := by
  intro hDA
  have hE : DifferentiallyAlgebraicOn reciprocalGammaEntire unitDiskDomain :=
    differentiallyAlgebraicOn_of_eqOn isOpen_unitDiskDomain hardyFun_hardyHTCarrier_eqOn hDA
  have huniv : DifferentiallyAlgebraicOn reciprocalGammaEntire (Set.univ : Set ℂ) :=
    differentiallyAlgebraicOn_of_subdomain isPreconnected_univ
      analyticOnNhd_reciprocalGammaEntire_univ (Set.subset_univ _) isOpen_unitDiskDomain
      nonempty_unitDiskDomain hE
  obtain ⟨n, P, hP0, hP⟩ := huniv
  exact FixedModulusRealRootedness.hypertranscendental_reciprocalGammaEntire
    ⟨n, P, hP0, fun z => hP z (Set.mem_univ z)⟩


/-! ## Density of the hypertranscendental phase -/

theorem analyticOnNhd_hardyFun (x : HardyDisk) :
    AnalyticOnNhd ℂ (hardyFun x) unitDiskDomain :=
  (Complex.analyticOnNhd_iff_differentiableOn isOpen_unitDiskDomain).2 (differentiableOn_hardyFun x)

theorem hardyFun_add_smul (a b : HardyDisk) (lam : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (a + lam • b) z = hardyFun a z + lam * hardyFun b z := by
  have hcoord : ∀ n : ℕ, ((a + lam • b : HardyDisk) : ℕ → ℂ) n
      = (a : ℕ → ℂ) n + lam * (b : ℕ → ℂ) n := by
    intro n
    simp
  have hA := summable_hardyDisk_terms a hz
  have hB := summable_hardyDisk_terms b hz
  have hAB : Summable (fun n => lam * ((b : ℕ → ℂ) n * z ^ n)) := hB.mul_left lam
  show ∑' n, ((a + lam • b : HardyDisk) : ℕ → ℂ) n * z ^ n
      = (∑' n, (a : ℕ → ℂ) n * z ^ n) + lam * ∑' n, (b : ℕ → ℂ) n * z ^ n
  have hsplit : ∀ n : ℕ, ((a + lam • b : HardyDisk) : ℕ → ℂ) n * z ^ n
      = (a : ℕ → ℂ) n * z ^ n + lam * ((b : ℕ → ℂ) n * z ^ n) := by
    intro n
    rw [hcoord n]
    ring
  rw [tsum_congr hsplit, hA.tsum_add hAB, tsum_mul_left]

theorem dense_compl_hardyDALocus : Dense ((hardyDALocus)ᶜ) := by
  classical
  have hopen := isOpen_unitDiskDomain
  have hconn := isPreconnected_unitDiskDomain
  have hnee := nonempty_unitDiskDomain
  have hinf := infinite_unitDiskDomain
  have hkey : ∀ (a : HardyDisk) (l1 l2 : ℂ), l1 ≠ l2 →
      (a + l1 • hardyHTCarrier) ∈ hardyDALocus →
      (a + l2 • hardyHTCarrier) ∈ hardyDALocus → False := by
    intro a l1 l2 hne h1 h2
    have hneg : DifferentiallyAlgebraicOn
        (fun z => (-1 : ℂ) * hardyFun (a + l2 • hardyHTCarrier) z) unitDiskDomain :=
      differentiallyAlgebraicOn_const_mul hopen hconn hnee hinf (-1)
        (analyticOnNhd_hardyFun _) h2
    have hsum := differentiallyAlgebraicOn_add hopen hconn hnee hinf
      (analyticOnNhd_hardyFun (a + l1 • hardyHTCarrier))
      (fun z hz => analyticAt_const.mul (analyticOnNhd_hardyFun _ z hz)) h1 hneg
    have heq : Set.EqOn
        (fun z => hardyFun (a + l1 • hardyHTCarrier) z
          + (-1 : ℂ) * hardyFun (a + l2 • hardyHTCarrier) z)
        (fun z => (l1 - l2) * hardyFun hardyHTCarrier z) unitDiskDomain := by
      intro z hz
      have hz' := mem_unitDiskDomain_iff.1 hz
      show hardyFun (a + l1 • hardyHTCarrier) z
          + (-1 : ℂ) * hardyFun (a + l2 • hardyHTCarrier) z
          = (l1 - l2) * hardyFun hardyHTCarrier z
      rw [hardyFun_add_smul a hardyHTCarrier l1 hz', hardyFun_add_smul a hardyHTCarrier l2 hz']
      ring
    have hdiff := differentiallyAlgebraicOn_of_eqOn hopen heq hsum
    have hfin := differentiallyAlgebraicOn_const_mul hopen hconn hnee hinf (l1 - l2)⁻¹
      (fun z hz => analyticAt_const.mul (analyticOnNhd_hardyFun hardyHTCarrier z hz)) hdiff
    refine not_differentiallyAlgebraicOn_hardyHTCarrier
      (differentiallyAlgebraicOn_of_eqOn hopen ?_ hfin)
    intro z _
    show (l1 - l2)⁻¹ * ((l1 - l2) * hardyFun hardyHTCarrier z) = hardyFun hardyHTCarrier z
    field_simp [sub_ne_zero.2 hne]
  rw [Metric.dense_iff]
  intro a ε hε
  set t : ℝ := ε / (2 * (‖hardyHTCarrier‖ + 1)) with htdef
  have hcnn : (0:ℝ) ≤ ‖hardyHTCarrier‖ := norm_nonneg _
  have htpos : 0 < t := by
    rw [htdef]
    positivity
  have hdist : ∀ lam : ℂ, ‖lam‖ = t → dist (a + lam • hardyHTCarrier) a < ε := by
    intro lam hlam
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hlam]
    have hlt : t * ‖hardyHTCarrier‖ < ε := by
      rw [htdef]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [hε, hcnn]
    exact hlt
  have hnorm1 : ‖((t : ℂ))‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hnorm2 : ‖(-(t : ℂ))‖ = t := by
    rw [norm_neg, hnorm1]
  have hne12 : ((t : ℂ)) ≠ (-(t : ℂ)) := by
    intro hcon
    have hre := congrArg Complex.re hcon
    simp at hre
    linarith
  by_cases hb : (a + ((t : ℂ)) • hardyHTCarrier) ∈ hardyDALocus
  · refine ⟨a + (-(t : ℂ)) • hardyHTCarrier, ?_, ?_⟩
    · rw [Metric.mem_ball]
      exact hdist _ hnorm2
    · intro hcon
      exact hkey a _ _ hne12 hb hcon
  · exact ⟨a + ((t : ℂ)) • hardyHTCarrier, by rw [Metric.mem_ball]; exact hdist _ hnorm1, hb⟩

/-- **The Hardy interlacing law.**  Both differential phases are norm dense in `H²(D)`, so no
norm-continuous map into a Hausdorff space that is constant on each phase can be nonconstant. -/
theorem hardy_phase_selector_collapse {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {Φ : HardyDisk → Y} (hΦ : Continuous Φ) {p q : Y}
    (hDA : ∀ a ∈ hardyDALocus, Φ a = p) (hHT : ∀ a ∈ (hardyDALocus)ᶜ, Φ a = q) :
    p = q ∧ Φ = fun _ => p := by
  have hpq : p = q :=
    const_eq_const_of_continuous_of_dense dense_hardyDALocus hΦ hDA hHT
      (dense_compl_hardyDALocus.nonempty)
  exact ⟨hpq, eq_const_of_continuous_of_dense_eqOn dense_hardyDALocus hΦ hDA⟩

end

end GaloisForLFunctions.HTGeometry
