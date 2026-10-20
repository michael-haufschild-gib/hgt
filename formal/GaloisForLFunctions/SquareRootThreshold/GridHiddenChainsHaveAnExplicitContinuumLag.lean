import GaloisForLFunctions.SquareRootThreshold.FiniteLagWindowRecordPotentialLaw
import GaloisForLFunctions.SquareRootThreshold.ChainsHideFromLagGrids

/-!
# Grid-hidden chains have an explicit continuum lag

The chain `Σ_n −c_n e^{λ_n v}`, `c_n = 2^{−(n+1)}`, `λ_n = δ_n + i(2π(n+1) + θ_n)`, `δ_n ↑ ¼`
not attained, has real part `≤ 0` at every integer lag (`re_gridChainSum_nat_nonpos`): it hides from
the grid `v ∈ ℕ`. Landau's theorem shows that it is unbounded on the continuum
(`not_bddAbove_re_gridChainSum`) but gives no lag. The finite Laplace window gives one.

**Abstract record-potential law** (`norm_coeff_mul_lapWin_le_of_le`). Let `Φ(u) = Σ_j p_j e^{μ_j u}`
with summable coefficients be real and `≤ M` on `[0, V]`. For every index `j₀` and `s = σ + it`,
`|p_{j₀} E_V(μ_{j₀} − s)| ≤ |M|(|E_V(−σ)| + |E_V(−s)|) + Σ_j |p_j||E_V(μ_j − σ)|
  + Σ_{j ≠ j₀} |p_j||E_V(μ_j − s)|`.
With a gap `η` of the exponents from the real axis and a gap `g` of the others from
`s = σ + i Im μ_{j₀}`, at `θ = Re μ_{j₀} − σ > 0` (`record_bound_of_le`):
`|p_{j₀}| (e^{θV} − 1)/θ ≤ 4|M|/σ + (1/η + 1/g) Σ_j |p_j| (e^{(Re μ_j − σ)V} + 1)`.
A real part `Re Σ q e^{λu}` is the real sum over the doubled family `λ, λ̄` with coefficients
`q/2, q̄/2` (`re_tsum_eq_doubled`).

**The chain** (`gridChain_lag_bound`, `exists_re_gridChainSum_gt`). At the lag `V = 2^{m+3}` the
Legendre record is the term `m`: with `x_n = 2^{m−n}`,
`c_n e^{δ_n V} = (e^{2^{m+1}}/2^{m+1}) x_n e^{−x_n}`, so the loudness is at most `4e` times the
record's (`gridChain_loudness_le`). The heights are `5`-separated from each other and from the
conjugates and `2π` away from the real axis. With `θ = 1/20` the law gives: if `Re Σ ≤ M` on
`[0, V]`, then `4 e^{V/20}/V ≤ 9|M| + 1`. So every level `M ≥ 0` is exceeded at some lag
`v ≤ 2^{m+3}` once `4 e^{2^{m+3}/20} > (9M + 1) 2^{m+3}`: the continuum lag of the level `M` is
`O(log M)`, while no integer lag ever sees the chain. The record replaces the attained top.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The abstract law -/

/-- `‖p e^{μu}‖ ≤ ‖p‖ e^{max(B,0) V}` for `Re μ ≤ B`, `u ∈ [0, V]`. -/
theorem norm_mul_cexp_le_of_mem_Icc {p μ : ℂ} {B V u : ℝ} (hB : μ.re ≤ B) (hu : u ∈ Icc (0 : ℝ) V) :
    ‖p * cexp (μ * u)‖ ≤ ‖p‖ * Real.exp (max B 0 * V) := by
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have e : (μ * (u : ℂ)).re = μ.re * u := by simp
  rw [e]
  calc μ.re * u ≤ max B 0 * u := mul_le_mul_of_nonneg_right (hB.trans (le_max_left _ _)) hu.1
    _ ≤ max B 0 * V := mul_le_mul_of_nonneg_left hu.2 (le_max_right _ _)

/-- **Termwise finite Laplace transform.** For summable `p` and `Re μ_j ≤ B`,
`∫_0^V Σ_j p_j e^{μ_j u} du = Σ_j p_j E_V(μ_j)`. -/
theorem integral_tsum_cexp_eq {J : Type*} [Countable J] {p μ : J → ℂ}
    (hp : Summable fun j => ‖p j‖) {B : ℝ} (hB : ∀ j, (μ j).re ≤ B) {V : ℝ} (hV : 0 ≤ V) :
    ∫ u in (0 : ℝ)..V, ∑' j, p j * cexp (μ j * u) = ∑' j, p j * lapWin V (μ j) := by
  set K : ℝ := V * Real.exp (max B 0 * V) with hK
  have hF : ∀ j, Integrable (fun u : ℝ => p j * cexp (μ j * u)) (volume.restrict (Ioc 0 V)) :=
    fun j => ((by fun_prop : Continuous fun u : ℝ => p j * cexp (μ j * u)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hsum : Summable fun j => ∫ u in Ioc 0 V, ‖p j * cexp (μ j * u)‖ := by
    refine Summable.of_nonneg_of_le (fun j => setIntegral_nonneg measurableSet_Ioc
      fun _ _ => norm_nonneg _) (fun j => ?_) (hp.mul_right K)
    rw [← intervalIntegral.integral_of_le hV]
    calc ∫ u in (0 : ℝ)..V, ‖p j * cexp (μ j * u)‖
        ≤ ∫ _u in (0 : ℝ)..V, ‖p j‖ * Real.exp (max B 0 * V) :=
          intervalIntegral.integral_mono_on hV ((by fun_prop : Continuous fun u : ℝ =>
            ‖p j * cexp (μ j * u)‖).intervalIntegrable _ _) intervalIntegrable_const
            fun u hu => norm_mul_cexp_le_of_mem_Icc (hB j) hu
      _ = ‖p j‖ * K := by simp [hK]
  rw [intervalIntegral.integral_of_le hV, ← integral_tsum_of_summable_integral_norm hF hsum]
  refine tsum_congr fun j => ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hV, lapWin]

/-- **Abstract record-potential law.** If `Φ(u) = Σ_j p_j e^{μ_j u}` is real and `≤ M` on `[0, V]`,
then for every `j₀` and `s = σ + it`,
`|p_{j₀} E_V(μ_{j₀} − s)| ≤ |M|(|E_V(−σ)| + |E_V(−s)|) + Σ_j |p_j||E_V(μ_j − σ)|
  + Σ_{j ≠ j₀} |p_j||E_V(μ_j − s)|`. -/
theorem norm_coeff_mul_lapWin_le_of_le {J : Type*} [Countable J] [DecidableEq J] {p μ : J → ℂ}
    (hp : Summable fun j => ‖p j‖) {B : ℝ} (hB : ∀ j, |(μ j).re| ≤ B) {V M : ℝ} (hV : 0 ≤ V)
    (him : ∀ u ∈ Icc (0 : ℝ) V, (∑' j, p j * cexp (μ j * u)).im = 0)
    (hle : ∀ u ∈ Icc (0 : ℝ) V, (∑' j, p j * cexp (μ j * u)).re ≤ M) (j₀ : J) (σ t : ℝ) :
    ‖p j₀ * lapWin V (μ j₀ - (σ + t * I))‖ ≤
      |M| * (‖lapWin V (-σ)‖ + ‖lapWin V (-(σ + t * I))‖) +
      ∑' j, ‖p j‖ * ‖lapWin V (μ j - σ)‖ +
      ∑' j, (if j = j₀ then 0 else ‖p j‖ * ‖lapWin V (μ j - (σ + t * I))‖) := by
  set Φ : ℝ → ℂ := fun u => ∑' j, p j * cexp (μ j * u) with hΦ
  have hBre : ∀ j, (μ j).re ≤ B := fun j => (le_abs_self _).trans (hB j)
  have hBs : ∀ (s : ℂ) j, (μ j - s).re ≤ B + |s.re| := fun s j => by
    rw [Complex.sub_re]; linarith [hBre j, neg_abs_le s.re]
  -- the window `G(s) = ∫_0^V e^{−su}(M − Re Φ)`, with `Re Φ = Φ` on `[0, V]`
  have hG : ∀ s : ℂ, ∫ u in (0 : ℝ)..V, cexp (-s * u) * ((M - (Φ u).re : ℝ) : ℂ) =
      M * lapWin V (-s) - ∑' j, p j * lapWin V (μ j - s) := by
    intro s
    have hcongr : ∀ u ∈ uIcc (0 : ℝ) V, cexp (-s * u) * ((M - (Φ u).re : ℝ) : ℂ) =
        M * cexp (-s * u) - ∑' j, p j * cexp ((μ j - s) * u) := fun u hu => by
      rw [uIcc_of_le hV] at hu
      have hΦr : (((Φ u).re : ℝ) : ℂ) = Φ u :=
        Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact (him u hu).symm)
      rw [Complex.ofReal_sub, hΦr, hΦ]
      simp only
      rw [mul_sub, ← tsum_mul_left, mul_comm]
      congr 1
      refine tsum_congr fun j => ?_
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    rw [intervalIntegral.integral_congr hcongr]
    have hsumj : Summable fun j => ‖p j‖ := hp
    have hcont : ContinuousOn (fun u : ℝ => ∑' j, p j * cexp ((μ j - s) * u)) (Icc 0 V) :=
      continuousOn_tsum (fun j => by fun_prop) (hp.mul_right (Real.exp (max (B + |s.re|) 0 * V)))
        fun j u hu => norm_mul_cexp_le_of_mem_Icc (hBs s j) hu
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u : ℝ => (M : ℂ) * cexp (-s * u)).intervalIntegrable _ _)
      ((hcont.mono (uIcc_of_le hV).le).intervalIntegrable),
      intervalIntegral.integral_const_mul, integral_tsum_cexp_eq hp (hBs s) hV, lapWin]
  have hg : ∀ u ∈ Icc (0 : ℝ) V, 0 ≤ M - (Φ u).re := fun u hu => by linarith [hle u hu]
  have hbound : ∀ s : ℂ, ∀ j, ‖lapWin V (μ j - s)‖ ≤ V * Real.exp ((B + |s.re|) * V) := fun s j =>
    (norm_lapWin_le_const hV _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by
        rw [Complex.sub_re]
        exact (abs_sub _ _).trans (by linarith [hB j])) hV)) hV)
  have hsumL : ∀ s : ℂ, Summable fun j => ‖p j‖ * ‖lapWin V (μ j - s)‖ := fun s =>
    (hp.mul_right (V * Real.exp ((B + |s.re|) * V))).of_nonneg_of_le
      (fun j => by positivity) fun j => mul_le_mul_of_nonneg_left (hbound s j) (norm_nonneg _)
  have hsumC : ∀ s : ℂ, Summable fun j => p j * lapWin V (μ j - s) := fun s =>
    (hsumL s).of_norm_bounded fun j => (norm_mul _ _).le
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hpos := norm_integral_cexp_mul_le hV hg s
  rw [hsre] at hpos
  have hGs := hG s
  have hGσ := hG σ
  have hsplit := (hsumC s).tsum_eq_add_tsum_ite j₀
  have hrest : ‖∑' j, (if j = j₀ then 0 else p j * lapWin V (μ j - s))‖ ≤
      ∑' j, (if j = j₀ then 0 else ‖p j‖ * ‖lapWin V (μ j - s)‖) := by
    have hn : ∀ j, ‖(if j = j₀ then 0 else p j * lapWin V (μ j - s))‖ =
        (if j = j₀ then 0 else ‖p j‖ * ‖lapWin V (μ j - s)‖) := fun j => by
      split_ifs <;> simp
    have hs' : Summable fun j => (if j = j₀ then 0 else ‖p j‖ * ‖lapWin V (μ j - s)‖) :=
      (hsumL s).of_nonneg_of_le (fun j => by split_ifs <;> positivity)
        fun j => by split_ifs <;> first | positivity | exact le_rfl
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hn)
    simp_rw [hn]
    exact hs'
  have hGre : (M * lapWin V (-(σ : ℂ)) - ∑' j, p j * lapWin V (μ j - σ)).re ≤
      |M| * ‖lapWin V (-σ)‖ + ∑' j, ‖p j‖ * ‖lapWin V (μ j - σ)‖ := by
    rw [Complex.sub_re]
    have h1 : (M * lapWin V (-(σ : ℂ))).re ≤ |M| * ‖lapWin V (-σ)‖ := by
      refine (Complex.re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : -(∑' j, p j * lapWin V (μ j - σ)).re ≤ ∑' j, ‖p j‖ * ‖lapWin V (μ j - σ)‖ := by
      refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
      refine (norm_tsum_le_tsum_norm (hsumC σ).norm).trans_eq ?_
      simp
    linarith
  set Gs := ∫ u in (0 : ℝ)..V, cexp (-s * u) * ((M - (Φ u).re : ℝ) : ℂ) with hGsdef
  set R := ∑' j, (if j = j₀ then 0 else p j * lapWin V (μ j - s)) with hRdef
  have hkey : p j₀ * lapWin V (μ j₀ - s) = M * lapWin V (-s) - Gs - R := by
    rw [hGs, hsplit]; ring
  rw [hkey]
  have htri : ‖M * lapWin V (-s) - Gs - R‖ ≤ ‖M * lapWin V (-s)‖ + ‖Gs‖ + ‖R‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_sub_le (M * lapWin V (-s)) Gs])
  have hMn : ‖(M : ℂ) * lapWin V (-s)‖ = |M| * ‖lapWin V (-s)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hGb : ‖Gs‖ ≤ |M| * ‖lapWin V (-σ)‖ + ∑' j, ‖p j‖ * ‖lapWin V (μ j - σ)‖ := by
    refine hpos.trans ?_
    rw [hGσ]
    exact hGre
  have hs1 : (-s : ℂ) = -(σ + t * I) := by rw [hs]
  rw [← hs1]
  linarith

/-- `|E_V(−σ)| ≤ 2/σ` and `|E_V(−s)| ≤ 2/σ` for `σ = Re s > 0`, `V ≥ 0`. -/
theorem norm_lapWin_neg_le {V : ℝ} (hV : 0 ≤ V) {s : ℂ} (hσ : 0 < s.re) :
    ‖lapWin V (-s)‖ ≤ 2 / s.re := by
  have hsn : s.re ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm s)
  have hne : -s ≠ 0 := fun h => by
    rw [neg_eq_zero] at h; rw [h, Complex.zero_re] at hσ; exact lt_irrefl _ hσ
  refine (norm_lapWin_le_div V hne).trans ?_
  rw [norm_neg]
  have : (-s).re * V ≤ 0 := by rw [Complex.neg_re]; nlinarith
  calc (Real.exp ((-s).re * V) + 1) / ‖s‖ ≤ 2 / ‖s‖ := by
        gcongr; linarith [Real.exp_le_one_iff.mpr this]
    _ ≤ 2 / s.re := div_le_div_of_nonneg_left (by norm_num) hσ hsn

/-- **Explicit record bound.** Under the hypotheses of `norm_coeff_mul_lapWin_le_of_le`, with a gap
`|Im μ_j| ≥ η` of the exponents from the real axis, a gap `g` of the others from
`s = σ + i Im μ_{j₀}`, `σ > 0` and `θ = Re μ_{j₀} − σ > 0`:
`|p_{j₀}| (e^{θV} − 1)/θ ≤ 4|M|/σ + (1/η + 1/g) Σ_j |p_j| (e^{(Re μ_j − σ)V} + 1)`. -/
theorem record_bound_of_le {J : Type*} [Countable J] [DecidableEq J] {p μ : J → ℂ}
    (hp : Summable fun j => ‖p j‖) {B : ℝ} (hB : ∀ j, |(μ j).re| ≤ B) {V M : ℝ} (hV : 0 ≤ V)
    (him : ∀ u ∈ Icc (0 : ℝ) V, (∑' j, p j * cexp (μ j * u)).im = 0)
    (hle : ∀ u ∈ Icc (0 : ℝ) V, (∑' j, p j * cexp (μ j * u)).re ≤ M) {j₀ : J} {σ η g : ℝ}
    (hσ : 0 < σ) (hθ : σ < (μ j₀).re) (hη : 0 < η) (hηj : ∀ j, η ≤ |(μ j).im|) (hg : 0 < g)
    (hsep : ∀ j, j ≠ j₀ → g ≤ ‖μ j - (σ + (μ j₀).im * I)‖) :
    ‖p j₀‖ * ((Real.exp (((μ j₀).re - σ) * V) - 1) / ((μ j₀).re - σ)) ≤
      4 * |M| / σ + (1 / η + 1 / g) * ∑' j, ‖p j‖ * (Real.exp (((μ j).re - σ) * V) + 1) := by
  classical
  set s : ℂ := σ + (μ j₀).im * I with hs
  set θ : ℝ := (μ j₀).re - σ with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hcore := norm_coeff_mul_lapWin_le_of_le hp hB hV him hle j₀ σ (μ j₀).im
  rw [← hs] at hcore
  have hz : μ j₀ - s = (θ : ℂ) := by apply Complex.ext <;> simp [hs, hθdef]
  have hLHS : ‖p j₀ * lapWin V (μ j₀ - s)‖ = ‖p j₀‖ * ((Real.exp (θ * V) - 1) / θ) := by
    rw [norm_mul, hz, norm_lapWin_ofReal_pos hV hθ0]
  have hE1 : ‖lapWin V (-(σ : ℂ))‖ ≤ 2 / σ := by
    have := norm_lapWin_neg_le hV (s := (σ : ℂ)) (by simpa using hσ); simpa using this
  have hE2 : ‖lapWin V (-s)‖ ≤ 2 / σ := by
    have := norm_lapWin_neg_le hV (s := s) (by simpa [hs] using hσ); simpa [hs] using this
  set T : ℝ := ∑' j, ‖p j‖ * (Real.exp (((μ j).re - σ) * V) + 1) with hT
  have hBre : ∀ j, (μ j).re ≤ B := fun j => (le_abs_self _).trans (hB j)
  have hsT : Summable fun j => ‖p j‖ * (Real.exp (((μ j).re - σ) * V) + 1) :=
    (hp.mul_right (Real.exp ((B + |σ|) * V) + 1)).of_nonneg_of_le (fun j => by positivity)
      fun j => mul_le_mul_of_nonneg_left (by
        gcongr
        linarith [hBre j, neg_abs_le σ]) (norm_nonneg _)
  have hkern : ∀ {j : J} {c : ℝ} {u : ℂ}, 0 < c → u.re = σ → c ≤ ‖μ j - u‖ →
      ‖p j‖ * ‖lapWin V (μ j - u)‖ ≤ ‖p j‖ * (Real.exp (((μ j).re - σ) * V) + 1) / c :=
    fun {j c u} hc hu hgap => by
      have := norm_lapWin_sub_le (V := V) hc hgap
      rw [hu] at this
      calc ‖p j‖ * ‖lapWin V (μ j - u)‖ ≤ ‖p j‖ * ((Real.exp (((μ j).re - σ) * V) + 1) / c) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by ring
  have hP1 : ∑' j, ‖p j‖ * ‖lapWin V (μ j - σ)‖ ≤ T / η := by
    rw [hT, ← tsum_div_const]
    have hle1 : ∀ j, ‖p j‖ * ‖lapWin V (μ j - σ)‖ ≤
        ‖p j‖ * (Real.exp (((μ j).re - σ) * V) + 1) / η := fun j =>
      hkern hη (by simp) ((hηj j).trans (by
        have := Complex.abs_im_le_norm (μ j - (σ : ℂ)); simpa using this))
    exact Summable.tsum_le_tsum hle1 ((hsT.div_const η).of_nonneg_of_le
      (fun _ => by positivity) hle1) (hsT.div_const η)
  have hP2 : ∑' j, (if j = j₀ then 0 else ‖p j‖ * ‖lapWin V (μ j - s)‖) ≤ T / g := by
    rw [hT, ← tsum_div_const]
    have hle2 : ∀ j, (if j = j₀ then 0 else ‖p j‖ * ‖lapWin V (μ j - s)‖) ≤
        ‖p j‖ * (Real.exp (((μ j).re - σ) * V) + 1) / g := fun j => by
      split_ifs with hj
      · positivity
      · exact hkern hg (by simp [hs]) (hsep j hj)
    exact Summable.tsum_le_tsum hle2 ((hsT.div_const g).of_nonneg_of_le
      (fun j => by split_ifs <;> positivity) hle2) (hsT.div_const g)
  rw [← hLHS]
  refine hcore.trans ?_
  have hM0 := abs_nonneg M
  have h1 : |M| * (‖lapWin V (-(σ : ℂ))‖ + ‖lapWin V (-s)‖) ≤ 4 * |M| / σ := by
    calc |M| * (‖lapWin V (-(σ : ℂ))‖ + ‖lapWin V (-s)‖) ≤ |M| * (2 / σ + 2 / σ) :=
          mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) hM0
      _ = 4 * |M| / σ := by ring
  have h2 : T / η + T / g = (1 / η + 1 / g) * T := by ring
  linarith

/-! ### The real part as a doubled exponential sum -/

/-- `Re Σ_t q_t e^{λ_t v} = Σ_T q'_T e^{λ'_T v}` over the doubled family `λ, λ̄` with coefficients
`q/2, q̄/2`; the doubled sum is real. -/
theorem re_tsum_eq_doubled {ι : Type*} {q lam : ι → ℂ} (hq : Summable fun t => ‖q t‖) {B : ℝ}
    (hB : ∀ t, |(lam t).re| ≤ B) (v : ℝ) :
    (((∑' t, q t * cexp (lam t * v)).re : ℝ) : ℂ) =
      ∑' T, doubledCoeff q T * cexp (doubledExp lam T * v) := by
  have hS : Summable fun t => q t * cexp (lam t * v) :=
    (hq.mul_right (Real.exp (B * |v|))).of_norm_bounded fun t => by
      rw [norm_mul, Complex.norm_exp]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have e : (lam t * (v : ℂ)).re = (lam t).re * v := by simp
      rw [e]
      exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB t)
        (abs_nonneg _))
  have hconj : ∀ t, conj (q t * cexp (lam t * v)) = conj (q t) * cexp (conj (lam t) * v) :=
    fun t => by rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have h1 : Summable fun t => doubledCoeff q (Sum.inl t) * cexp (doubledExp lam (Sum.inl t) * v) :=
    (hS.div_const 2).congr fun t => by simp only [doubledCoeff_inl, doubledExp_inl]; ring
  have h2 : Summable fun t => doubledCoeff q (Sum.inr t) * cexp (doubledExp lam (Sum.inr t) * v) :=
    ((Summable.of_norm_bounded (f := fun t => conj (q t) * cexp (conj (lam t) * v)) hS.norm
      fun t => by rw [← hconj, Complex.norm_conj]).div_const 2).congr fun t => by
        simp only [doubledCoeff_inr, doubledExp_inr]; ring
  rw [Summable.tsum_sum (f := fun T => doubledCoeff q T * cexp (doubledExp lam T * v)) h1 h2]
  have e1 : ∑' t, doubledCoeff q (Sum.inl t) * cexp (doubledExp lam (Sum.inl t) * v) =
      (∑' t, q t * cexp (lam t * v)) / 2 := by
    rw [← tsum_div_const]
    exact tsum_congr fun t => by simp only [doubledCoeff_inl, doubledExp_inl]; ring
  have e2 : ∑' t, doubledCoeff q (Sum.inr t) * cexp (doubledExp lam (Sum.inr t) * v) =
      conj (∑' t, q t * cexp (lam t * v)) / 2 := by
    rw [Complex.conj_tsum, ← tsum_div_const]
    exact tsum_congr fun t => by simp only [doubledCoeff_inr, doubledExp_inr, hconj]; ring
  rw [e1, e2, Complex.re_eq_add_conj]
  ring

end GaloisForLFunctions.SquareRootThreshold
