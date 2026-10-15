import GaloisForLFunctions.RHTower.EvenSectorAbelPinning

/-!
# Even Weil positivity at any pole weight: Abel rigidity

**Theorem** (`riemannHypothesis_of_weilPositiveEvenAt_of_abel`).  Let real weights `lam` be
Weil-positive at some pole weight `β` on every autocorrelation of an even compactly supported `C²`
test.  If `Σ |lam(n)| n^{−σ} < ∞` for every `σ > 1`, and `F(s) = Σ_{n ≥ 2} lam(n) n^{−1−s}` has no
negative double pole at `s = 0` (`s² F(s) ≥ −ε` for small `s > 0`), then RH holds and `lam = Λ` on
`n ≥ 2`.

So an even-positive weight system at a pole weight `β > 1` different from `Λ` must either have a
Dirichlet series that diverges absolutely somewhere on `Re s > 1` (a real pole in `(1, 3/2]`), or
a negative double pole at `s = 1`.

**Corollary** (`riemannHypothesis_iff_exists_nonneg_weilPositiveEvenAt`).  RH holds iff some
NONNEGATIVE weight system is Weil-positive on even tests at some pole weight.  Nonnegative weights
converge absolutely on `Re s > 1` because the even far bumps bound their window sums by
`O(e^a)` (`exists_sum_Ioc_le_of_weilPositiveEvenAt_of_nonneg`), and their `F(s)` is nonnegative.

Proof of the theorem: `realWeil_nonneg_of_abel` (Abel averaging of the pole-free far-bump
corrections, the even ceiling, and the two-scale iteration) gives `W(g) ≥ 0` for every real even
test; real tests suffice (`weilPositiveEvenAt_one_of_real`), and even positivity at pole weight one
is RH with `lam = Λ` (`weilPositiveEvenAt_one_iff`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight WeilWorkPBAP Finsupp

theorem exists_abs_gt_eq_zero_of_hasCompactSupport {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < |x| → g x = 0 := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R|, abs_nonneg R, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_abs_self R]

/-- **The Abel limit of the far-bump inequality.**  If `s · s F(s) → 0`, then for every real even
test `g`, `W(g) ≥ P² (2 − 4X(s) + 2X(s/2)) − ε` for all small `s`, `X(s) = s F(s)`. -/
theorem eventually_realWeil_ge {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hX : Tendsto (fun s => s * (s * oddDirichlet lam s)) (𝓝[>] 0) (𝓝 0))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgs : ∀ x, R < |x| → g x = 0)
    (hge : ∀ x, g (-x) = g x) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ x, g x * Real.exp (-x / 2)) ^ 2 * (2 - 4 * (s * oddDirichlet lam s) +
          2 * (s / 2 * oddDirichlet lam (s / 2))) - ε ≤
        (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  obtain ⟨M, hM0, hM⟩ := abel_averaged_ineq hpf hsl hg hR hgs hge
  obtain ⟨C, hC0, hC⟩ := abel_bounds hsl hg hR hgs hge
  exact eventually_ge_of_abel_data (J := farJ) farJ_pos hM0 hC0
    (I₀ := fun s => ∫ a in Ici (R + 1), farAbelWeight s a)
    (A₁ := fun s => ∫ a in Ici (R + 1), farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a))
    (A₂ := fun s => ∫ a in Ici (R + 1),
      farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a))
    (A₃ := fun s => ∫ a in Ici (R + 1), farSum lam a * Real.exp (-(1 + s) * a))
    (E₁ := fun s => (∫ a in Ici (R + 1), Real.exp (-(1 / 2 + s) * a)) +
      ∫ a in Ici (R + 1), Real.exp (-(1 / 2 + (1 + s)) * a))
    (E₂ := fun s => ∫ a in Ici (R + 1), Real.exp (-(1 + s) * a))
    (X := fun s => s * oddDirichlet lam s)
    (fun s hs _ => hM s hs) (fun s hs hs2 => hC s hs hs2) hX

/-- **Real even tests are nonnegative** under even pole-free positivity, absolute convergence on
`Re s > 1`, the Abel ceiling `s F(s) ≤ 1 + o(1)` and no negative double pole. -/
theorem realWeil_nonneg_of_polar {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hup : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), s * oddDirichlet lam s ≤ 1 + ε)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hge : ∀ x, g (-x) = g x) :
    0 ≤ (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  obtain ⟨R, hR, hgs⟩ := exists_abs_gt_eq_zero_of_hasCompactSupport hgc
  have hX := tendsto_mul_of_two_sided (X := fun s => s * oddDirichlet lam s) hup hdp
  exact nonneg_of_two_scale (X := fun s => s * oddDirichlet lam s) hup hdp
    (eventually_realWeil_ge hpf hsl hX hg hR hgs hge)

/-- **Real even tests are nonnegative** under even positivity at any pole weight, absolute
convergence on `Re s > 1` and no negative double pole. -/
theorem realWeil_nonneg_of_abel {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hge : ∀ x, g (-x) = g x) :
    0 ≤ (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re :=
  realWeil_nonneg_of_polar (weilPositiveEvenPolar_of_weilPositiveEvenAt h) hsl
    (eventually_le_one_add_of_weilPositiveEvenAt h hsl) hdp hg hgc hge

/-- **Real even tests suffice for even positivity at pole weight one.** -/
theorem weilPositiveEvenAt_one_of_real {lam : ℕ → ℝ}
    (h : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → (∀ x, g (-x) = g x) →
      0 ≤ (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re) :
    WeilPositiveEvenAt 1 lam := by
  intro f hf hfc hfe
  rw [re_weilPoleWeightFunctional_eq_add, sub_self, zero_mul, add_zero]
  set F : WeilTestFn := ⟨f, hf, hfc⟩ with hFdef
  set Rf := paperRealPartTestFn F with hRf
  set Jf := paperImagPartTestFn F with hJf
  have hsplit : paperSplitRealMixture (Finsupp.single F 1) =
      Finsupp.single Rf 1 + Finsupp.single Jf 1 := by
    simp [paperSplitRealMixture, hRf, hJf, Finsupp.mapDomain_single]
  have hE := energy_paperSplitRealMixture (Finsupp.single F 1)
  have hD := defect_paperSplitRealMixture (Finsupp.single F 1)
  rw [hsplit] at hE hD
  simp only [energy, defect, map_add, linearCombination_single, one_smul] at hE hD
  have hF := re_weilFullFunctional_eq lam F
  have hRe := re_weilFullFunctional_eq lam Rf
  have hIm := re_weilFullFunctional_eq lam Jf
  have hRpos := h (fun x => (f x).re) (Complex.reCLM.contDiff.comp hf)
    (hfc.comp_left (g := fun z : ℂ => z.re) (by simp)) (fun x => by simp only [hfe])
  have hJpos := h (fun x => (f x).im) (Complex.imCLM.contDiff.comp hf)
    (hfc.comp_left (g := fun z : ℂ => z.im) (by simp)) (fun x => by simp only [hfe])
  have hRe' : (weilFullFunctional lam (EF.weilTest Rf.1 Rf.1)).re =
      (weilFullFunctional lam
        (EF.weilTest (fun u => ((f u).re : ℂ)) (fun u => ((f u).re : ℂ)))).re := rfl
  have hIm' : (weilFullFunctional lam (EF.weilTest Jf.1 Jf.1)).re =
      (weilFullFunctional lam
        (EF.weilTest (fun u => ((f u).im : ℂ)) (fun u => ((f u).im : ℂ)))).re := rfl
  have hfF : (weilFullFunctional lam (EF.weilTest f f)).re =
      (weilFullFunctional lam (EF.weilTest F.1 F.1)).re := rfl
  rw [hfF, hF, ← hE, ← hD, map_add]
  have : (weilFullFunctional lam (EF.weilTest Rf.1 Rf.1)).re +
      (weilFullFunctional lam (EF.weilTest Jf.1 Jf.1)).re =
      weilArchRe (EF.weilTest Rf.1 Rf.1) + weilArchRe (EF.weilTest Jf.1 Jf.1) -
        ((linearCombination ℝ (fun j : LogIndex => lam j)) (logVector Rf) +
          (linearCombination ℝ (fun j : LogIndex => lam j)) (logVector Jf)) := by
    rw [hRe, hIm]; ring
  rw [← this, hRe', hIm']
  exact add_nonneg hRpos hJpos

/-- **Abel rigidity of the even cone.**  Even positivity at some pole weight, absolute convergence
on `Re s > 1` and no negative double pole at `s = 1` give even positivity at pole weight one. -/
theorem weilPositiveEvenAt_one_of_abel {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s)) :
    WeilPositiveEvenAt 1 lam :=
  weilPositiveEvenAt_one_of_real fun _ hg hgc hge => realWeil_nonneg_of_abel h hsl hdp hg hgc hge

/-- **RH from even positivity without super-poles and negative double poles.** -/
theorem riemannHypothesis_of_weilPositiveEvenAt_of_abel {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hdp : ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s)) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_abel h hsl hdp)

/-! ## Nonnegative weights -/

/-- The even far bumps bound the window sums: `S(a) ≤ |β| ((e^{−a/2} + e^{a/2}) J)² + A₁`. -/
theorem farSum_le_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveEvenAt β lam)
    {a : ℝ} (ha : 0 ≤ a) :
    farSum lam a ≤ |β| * ((Real.exp (-a / 2) + Real.exp (a / 2)) * farJ) ^ 2 +
      1 / (4 * Real.pi) * farBumpArchMass := by
  have hc := continuous_evenFarBump a
  have hcs := hasCompactSupport_evenFarBump a
  have he : ∀ x, evenFarBump a (-x) = evenFarBump a x := evenFarBump_neg a
  have hpos := h (fun u => (evenFarBump a u : ℂ)) (contDiff_ofReal_comp (contDiff_evenFarBump a))
    (hcs.comp_left Complex.ofReal_zero) (fun x => by simp only [he])
  rw [re_weilPoleWeightFunctional_eq_add, re_weilFullFunctional_ofReal_eq lam hc hcs,
    re_weilPoleTerm_ofReal_even hc hcs he, integral_evenFarBump_mul_exp,
    atomPairing_evenFarBump lam ha] at hpos
  have hA := abs_le.mp (abs_farArch_evenFarBump_le a)
  have hb := le_abs_self β
  have hsq := sq_nonneg ((Real.exp (-a / 2) + Real.exp (a / 2)) * farJ)
  have e : 1 / (2 * Real.pi) * farBumpArchMass = 2 * (1 / (4 * Real.pi) * farBumpArchMass) := by
    field_simp; ring
  nlinarith

/-- **Window bound for nonnegative even-positive weights:** `Σ_{N < n ≤ 2N} lam(n) ≤ B N`. -/
theorem exists_sum_Ioc_le_of_weilPositiveEvenAt_of_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), lam n ≤ B * N := by
  have hr : 0 < (nodeBump 2).rIn := (nodeBump 2).rIn_pos
  set C₁ := 1 / (4 * Real.pi) * farBumpArchMass with hC₁
  set U₀ := 12 * |β| * farJ ^ 2 + 2 * |C₁| with hU₀
  refine ⟨((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * U₀, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 := Real.log_two_gt_d9
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  set Emax := Real.exp ((Real.log N + Real.log 2 + 1 / 12) / 2) with hEmax
  have hEmax : Real.sqrt (2 * N) * Emax ≤ 3 * N := by
    have h1 : (Real.sqrt (2 * N) * Emax) ^ 2 = 2 * N * (2 * N * Real.exp (1 / 12)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hEmax, ← Real.exp_nat_mul]
      rw [show ((2 : ℕ) : ℝ) * ((Real.log N + Real.log 2 + 1 / 12) / 2) =
        Real.log N + Real.log 2 + 1 / 12 by push_cast; ring, Real.exp_add, Real.exp_add,
        Real.exp_log hN0, Real.exp_log two_pos]
      ring
    have h2 : Real.exp (1 / 12) ≤ 2 := by
      have hm : Real.exp (1 / 12) * Real.exp (-(1 / 12)) = 1 := by rw [← Real.exp_add]; simp
      have := Real.add_one_le_exp (-(1 / 12))
      nlinarith [Real.exp_pos (1 / 12)]
    have h3 : (Real.sqrt (2 * N) * Emax) ^ 2 ≤ (3 * N) ^ 2 := by rw [h1]; nlinarith
    have h4 : 0 ≤ Real.sqrt (2 * N) * Emax := by positivity
    nlinarith
  -- each window
  have hwin : ∀ i ∈ Finset.range (farWindowCount + 1),
      ∑ n ∈ Finset.Ioc N (2 * N), lam n / Real.sqrt n * farKernel (Real.log n - 2 * farWindow N i)
        ≤ 4 * |β| * farJ ^ 2 * Emax + |C₁| := by
    intro i hi
    obtain ⟨h1, h2⟩ := farWindow_bounds N (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have ha0 : 0 ≤ farWindow N i := by linarith
    have hS := farSum_le_of_weilPositiveEvenAt h ha0
    rw [farSum_eq_sum hN h2] at hS
    have hsub : Finset.Ioc N (2 * N) ⊆ Finset.Icc 2 (4 * N) := fun n hn => by
      rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun n =>
      lam n / Real.sqrt n * farKernel (Real.log n - 2 * farWindow N i)) fun n hn _ =>
      mul_nonneg (div_nonneg (hnn n (Finset.mem_Icc.mp hn).1) (Real.sqrt_nonneg _))
        (farKernel_nonneg _)
    have hE : (Real.exp (-farWindow N i / 2) + Real.exp (farWindow N i / 2)) ^ 2 ≤
        4 * Real.exp (farWindow N i) := by
      have h3 : Real.exp (-farWindow N i / 2) ≤ Real.exp (farWindow N i / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have h4 : Real.exp (farWindow N i / 2) ^ 2 = Real.exp (farWindow N i) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      nlinarith [Real.exp_pos (-farWindow N i / 2)]
    have hEm : Real.exp (farWindow N i) ≤ Emax := Real.exp_le_exp.mpr (by linarith)
    have h5 : |β| * ((Real.exp (-farWindow N i / 2) + Real.exp (farWindow N i / 2)) * farJ) ^ 2 ≤
        4 * |β| * farJ ^ 2 * Emax := by
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_right (hE.trans (mul_le_mul_of_nonneg_left hEm (by norm_num)))
        (sq_nonneg farJ)
      have hb := abs_nonneg β
      nlinarith
    linarith [le_abs_self C₁]
  -- cover
  have hcov : (nodeBump 2).rIn * ∑ n ∈ Finset.Ioc N (2 * N), lam n / Real.sqrt n ≤
      ∑ i ∈ Finset.range (farWindowCount + 1), ∑ n ∈ Finset.Ioc N (2 * N),
        lam n / Real.sqrt n * farKernel (Real.log n - 2 * farWindow N i) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    rw [← Finset.mul_sum]
    calc (nodeBump 2).rIn * (lam n / Real.sqrt n)
        = lam n / Real.sqrt n * (nodeBump 2).rIn := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (farWindow_cover hN hn1 hn2)
          (div_nonneg (hnn n (by omega)) (Real.sqrt_nonneg _))
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have h1 : ∑ n ∈ Finset.Ioc N (2 * N), lam n / Real.sqrt n ≤
      ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * (4 * |β| * farJ ^ 2 * Emax + |C₁|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    have := hcov.trans hsum
    push_cast at this
    linarith
  have h2 : ∀ n ∈ Finset.Ioc N (2 * N), lam n ≤ Real.sqrt (2 * N) * (lam n / Real.sqrt n) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsn := Real.sqrt_pos.mpr hn0
    have hle : Real.sqrt n ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt (by exact_mod_cast hn2)
    rw [mul_div_assoc', le_div_iff₀ hsn]
    exact (mul_le_mul_of_nonneg_left hle (hnn n (by omega))).trans_eq (by ring)
  have hsqN : Real.sqrt (2 * N) ≤ 2 * N := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hq : 0 ≤ ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn := by positivity
  calc ∑ n ∈ Finset.Ioc N (2 * N), lam n
      ≤ ∑ n ∈ Finset.Ioc N (2 * N), Real.sqrt (2 * N) * (lam n / Real.sqrt n) :=
        Finset.sum_le_sum h2
    _ = Real.sqrt (2 * N) * ∑ n ∈ Finset.Ioc N (2 * N), lam n / Real.sqrt n := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt (2 * N) * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (4 * |β| * farJ ^ 2 * Emax + |C₁|)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (4 * |β| * farJ ^ 2 * (Real.sqrt (2 * N) * Emax) + Real.sqrt (2 * N) * |C₁|) := by
        ring
    _ ≤ ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (4 * |β| * farJ ^ 2 * (3 * N) + 2 * N * |C₁|) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hq
        · exact mul_le_mul_of_nonneg_left hEmax (by positivity)
        · exact mul_le_mul_of_nonneg_right hsqN (abs_nonneg _)
    _ = ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * U₀ * N := by rw [hU₀]; ring

theorem summable_abs_div_rpow_of_weilPositiveEvenAt_of_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  obtain ⟨B, hB0, hB⟩ := exists_sum_Ioc_le_of_weilPositiveEvenAt_of_nonneg h hnn
  refine summable_div_rpow_of_block (fun n => abs_nonneg (lam n)) (B := B) (j₀ := 1) hσ
    fun j hj => ?_
  have hN : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring]
  have e : ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), |lam n| =
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), lam n := by
    refine Finset.sum_congr rfl fun n hn => abs_of_nonneg (hnn n ?_)
    have h2 : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have := (Finset.mem_Ioc.mp hn).1
    omega
  rw [e]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), lam n ≤ B * ((2 ^ j : ℕ) : ℝ) := hB _ hN
    _ ≤ B * 2 ^ j * ((j : ℝ) + 1) := by
        push_cast
        have : (0 : ℝ) ≤ B * 2 ^ j := by positivity
        nlinarith

theorem oddDirichlet_nonneg_of_nonneg {lam : ℕ → ℝ} (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) (s : ℝ) :
    0 ≤ oddDirichlet lam s := by
  unfold oddDirichlet
  refine tsum_nonneg fun n => div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  split_ifs with hn
  · exact hnn n hn
  · exact le_rfl

/-- **Even rigidity for nonnegative weights.**  A nonnegative weight system that is Weil-positive on
even tests at some pole weight is `Λ`, and RH holds. -/
theorem riemannHypothesis_of_weilPositiveEvenAt_of_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine riemannHypothesis_of_weilPositiveEvenAt_of_abel h
    (fun σ hσ => summable_abs_div_rpow_of_weilPositiveEvenAt_of_nonneg h hnn hσ) fun ε hε => ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s := hs
  have := oddDirichlet_nonneg_of_nonneg hnn s
  have : 0 ≤ s * (s * oddDirichlet lam s) := by positivity
  linarith

/-- **RH is even positivity of a nonnegative weight system at some pole weight.** -/
theorem riemannHypothesis_iff_exists_nonneg_weilPositiveEvenAt :
    RiemannHypothesis ↔ ∃ (β : ℝ) (lam : ℕ → ℝ), (∀ n, 2 ≤ n → 0 ≤ lam n) ∧
      WeilPositiveEvenAt β lam := by
  constructor
  · intro hRH
    exact ⟨1, fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      fun n _ => ArithmeticFunction.vonMangoldt_nonneg,
      weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩⟩
  · rintro ⟨β, lam, hnn, h⟩
    exact (riemannHypothesis_of_weilPositiveEvenAt_of_nonneg h hnn).1

/-! ## Weights bounded below -/

theorem sum_farKernel_div_sqrt_le {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : Real.log N ≤ 2 * a) :
    ∑ n ∈ Finset.Icc 2 (4 * N), farKernel (Real.log n - 2 * a) / Real.sqrt n ≤
      4 * N * (farMass * Real.sqrt (2 / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hK0 : 0 ≤ farMass := (farKernel_nonneg 0).trans (farKernel_le 0)
  have hpt : ∀ n ∈ Finset.Icc 2 (4 * N),
      farKernel (Real.log n - 2 * a) / Real.sqrt n ≤ farMass * Real.sqrt (2 / N) := by
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rcases le_or_gt ((n : ℝ)) (N / 2) with hle | hlt
    · have hl : Real.log n ≤ Real.log N - Real.log 2 := by
        rw [← Real.log_div hN0.ne' (by norm_num)]
        exact Real.log_le_log hn0 hle
      have hr := nodeBump_rOut_le 2
      have hlog2 := Real.log_two_gt_d9
      rw [farKernel_eq_zero (by rw [abs_of_nonpos (by linarith)]; linarith), zero_div]
      positivity
    · have hsq : (Real.sqrt n)⁻¹ ≤ Real.sqrt (2 / N) := by
        rw [show Real.sqrt (2 / N) = (Real.sqrt (N / 2))⁻¹ by
          rw [← Real.sqrt_inv, inv_div]]
        exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hlt.le)
      rw [div_eq_mul_inv]
      exact mul_le_mul (farKernel_le _) hsq (by positivity) hK0
  calc ∑ n ∈ Finset.Icc 2 (4 * N), farKernel (Real.log n - 2 * a) / Real.sqrt n
      ≤ (Finset.Icc 2 (4 * N)).card • (farMass * Real.sqrt (2 / N)) :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ ≤ 4 * N * (farMass * Real.sqrt (2 / N)) := by
        rw [nsmul_eq_mul, Nat.card_Icc]
        have : ((4 * N + 1 - 2 : ℕ) : ℝ) ≤ 4 * N := by
          have h1 : 4 * N + 1 - 2 ≤ 4 * N := by omega
          exact_mod_cast h1
        exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **Window bound for even-positive weights bounded below:** `Σ_{N < n ≤ 2N} (lam(n) + C) ≤ B N`
when `lam ≥ −C`. -/
theorem exists_sum_Ioc_add_le_of_weilPositiveEvenAt_of_ge {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {C : ℝ} (hC : 0 ≤ C) (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Ioc N (2 * N), (lam n + C) ≤ B * N := by
  have hr : 0 < (nodeBump 2).rIn := (nodeBump 2).rIn_pos
  have hK0 : 0 ≤ farMass := (farKernel_nonneg 0).trans (farKernel_le 0)
  set C₁ := 1 / (4 * Real.pi) * farBumpArchMass with hC₁
  set U₀ := 12 * |β| * farJ ^ 2 + 2 * |C₁| + 8 * C * farMass with hU₀
  refine ⟨((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * U₀, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 := Real.log_two_gt_d9
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnn : ∀ n, 2 ≤ n → 0 ≤ lam n + C := fun n hn => by linarith [hlb n hn]
  set Emax := Real.exp ((Real.log N + Real.log 2 + 1 / 12) / 2) with hEmax
  set V := C * (4 * N * (farMass * Real.sqrt (2 / N))) with hV
  have hEmax : Real.sqrt (2 * N) * Emax ≤ 3 * N := by
    have h1 : (Real.sqrt (2 * N) * Emax) ^ 2 = 2 * N * (2 * N * Real.exp (1 / 12)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hEmax, ← Real.exp_nat_mul]
      rw [show ((2 : ℕ) : ℝ) * ((Real.log N + Real.log 2 + 1 / 12) / 2) =
        Real.log N + Real.log 2 + 1 / 12 by push_cast; ring, Real.exp_add, Real.exp_add,
        Real.exp_log hN0, Real.exp_log two_pos]
      ring
    have h2 : Real.exp (1 / 12) ≤ 2 := by
      have hm : Real.exp (1 / 12) * Real.exp (-(1 / 12)) = 1 := by rw [← Real.exp_add]; simp
      have := Real.add_one_le_exp (-(1 / 12))
      nlinarith [Real.exp_pos (1 / 12)]
    have h3 : (Real.sqrt (2 * N) * Emax) ^ 2 ≤ (3 * N) ^ 2 := by rw [h1]; nlinarith
    have h4 : 0 ≤ Real.sqrt (2 * N) * Emax := by positivity
    nlinarith
  have hV2 : Real.sqrt (2 * N) * V = 8 * C * farMass * N := by
    have : Real.sqrt (2 * N) * Real.sqrt (2 / N) = 2 := by
      rw [← Real.sqrt_mul (by positivity), show 2 * (N : ℝ) * (2 / N) = 2 ^ 2 by field_simp,
        Real.sqrt_sq (by norm_num)]
    rw [hV]
    calc Real.sqrt (2 * N) * (C * (4 * N * (farMass * Real.sqrt (2 / N))))
        = C * 4 * N * farMass * (Real.sqrt (2 * N) * Real.sqrt (2 / N)) := by ring
      _ = 8 * C * farMass * N := by rw [this]; ring
  -- each window
  have hwin : ∀ i ∈ Finset.range (farWindowCount + 1),
      ∑ n ∈ Finset.Ioc N (2 * N), (lam n + C) / Real.sqrt n *
          farKernel (Real.log n - 2 * farWindow N i) ≤
        4 * |β| * farJ ^ 2 * Emax + |C₁| + V := by
    intro i hi
    obtain ⟨h1, h2⟩ := farWindow_bounds N (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have ha0 : 0 ≤ farWindow N i := by linarith
    have hS := farSum_le_of_weilPositiveEvenAt h ha0
    rw [farSum_eq_sum hN h2] at hS
    have hsub : Finset.Ioc N (2 * N) ⊆ Finset.Icc 2 (4 * N) := fun n hn => by
      rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun n =>
      (lam n + C) / Real.sqrt n * farKernel (Real.log n - 2 * farWindow N i)) fun n hn _ =>
      mul_nonneg (div_nonneg (hnn n (Finset.mem_Icc.mp hn).1) (Real.sqrt_nonneg _))
        (farKernel_nonneg _)
    have hsplit : ∑ n ∈ Finset.Icc 2 (4 * N), (lam n + C) / Real.sqrt n *
        farKernel (Real.log n - 2 * farWindow N i) =
        ∑ n ∈ Finset.Icc 2 (4 * N), lam n / Real.sqrt n *
          farKernel (Real.log n - 2 * farWindow N i) +
        C * ∑ n ∈ Finset.Icc 2 (4 * N), farKernel (Real.log n - 2 * farWindow N i) /
          Real.sqrt n := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have hKs := sum_farKernel_div_sqrt_le hN h1
    have hCK := mul_le_mul_of_nonneg_left hKs hC
    have hE : (Real.exp (-farWindow N i / 2) + Real.exp (farWindow N i / 2)) ^ 2 ≤
        4 * Real.exp (farWindow N i) := by
      have h3 : Real.exp (-farWindow N i / 2) ≤ Real.exp (farWindow N i / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have h4 : Real.exp (farWindow N i / 2) ^ 2 = Real.exp (farWindow N i) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      nlinarith [Real.exp_pos (-farWindow N i / 2)]
    have hEm : Real.exp (farWindow N i) ≤ Emax := Real.exp_le_exp.mpr (by linarith)
    have h5 : |β| * ((Real.exp (-farWindow N i / 2) + Real.exp (farWindow N i / 2)) * farJ) ^ 2 ≤
        4 * |β| * farJ ^ 2 * Emax := by
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_right (hE.trans (mul_le_mul_of_nonneg_left hEm (by norm_num)))
        (sq_nonneg farJ)
      have hb := abs_nonneg β
      nlinarith
    rw [hsplit] at hmono
    linarith [le_abs_self C₁]
  -- cover
  have hcov : (nodeBump 2).rIn * ∑ n ∈ Finset.Ioc N (2 * N), (lam n + C) / Real.sqrt n ≤
      ∑ i ∈ Finset.range (farWindowCount + 1), ∑ n ∈ Finset.Ioc N (2 * N),
        (lam n + C) / Real.sqrt n * farKernel (Real.log n - 2 * farWindow N i) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    rw [← Finset.mul_sum]
    calc (nodeBump 2).rIn * ((lam n + C) / Real.sqrt n)
        = (lam n + C) / Real.sqrt n * (nodeBump 2).rIn := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (farWindow_cover hN hn1 hn2)
          (div_nonneg (hnn n (by omega)) (Real.sqrt_nonneg _))
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have h1 : ∑ n ∈ Finset.Ioc N (2 * N), (lam n + C) / Real.sqrt n ≤
      ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * (4 * |β| * farJ ^ 2 * Emax + |C₁| + V) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    have := hcov.trans hsum
    push_cast at this
    linarith
  have h2 : ∀ n ∈ Finset.Ioc N (2 * N),
      lam n + C ≤ Real.sqrt (2 * N) * ((lam n + C) / Real.sqrt n) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsn := Real.sqrt_pos.mpr hn0
    have hle : Real.sqrt n ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt (by exact_mod_cast hn2)
    rw [mul_div_assoc', le_div_iff₀ hsn]
    exact (mul_le_mul_of_nonneg_left hle (hnn n (by omega))).trans_eq (by ring)
  have hsqN : Real.sqrt (2 * N) ≤ 2 * N := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hq : 0 ≤ ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn := by positivity
  calc ∑ n ∈ Finset.Ioc N (2 * N), (lam n + C)
      ≤ ∑ n ∈ Finset.Ioc N (2 * N), Real.sqrt (2 * N) * ((lam n + C) / Real.sqrt n) :=
        Finset.sum_le_sum h2
    _ = Real.sqrt (2 * N) * ∑ n ∈ Finset.Ioc N (2 * N), (lam n + C) / Real.sqrt n := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt (2 * N) * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (4 * |β| * farJ ^ 2 * Emax + |C₁| + V)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (4 * |β| * farJ ^ 2 * (Real.sqrt (2 * N) * Emax) + Real.sqrt (2 * N) * |C₁| +
          Real.sqrt (2 * N) * V) := by ring
    _ ≤ ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (4 * |β| * farJ ^ 2 * (3 * N) + 2 * N * |C₁| + 8 * C * farMass * N) := by
        rw [hV2]
        refine mul_le_mul_of_nonneg_left (add_le_add_three ?_ ?_ le_rfl) hq
        · exact mul_le_mul_of_nonneg_left hEmax (by positivity)
        · exact mul_le_mul_of_nonneg_right hsqN (abs_nonneg _)
    _ = ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * U₀ * N := by rw [hU₀]; ring

theorem summable_abs_div_rpow_of_weilPositiveEvenAt_of_ge {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {C : ℝ} (hC : 0 ≤ C) (hlb : ∀ n, 2 ≤ n → -C ≤ lam n)
    {σ : ℝ} (hσ : 1 < σ) : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  obtain ⟨B, hB0, hB⟩ := exists_sum_Ioc_add_le_of_weilPositiveEvenAt_of_ge h hC hlb
  refine summable_div_rpow_of_block (fun n => abs_nonneg (lam n)) (B := B + C) (j₀ := 1) hσ
    fun j hj => ?_
  have hN : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h2 : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring]
  have hle : ∀ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), |lam n| ≤ (lam n + C) + C := by
    intro n hn
    have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have := hlb n hn2
    rcases le_total 0 (lam n) with h0 | h0
    · rw [abs_of_nonneg h0]; linarith
    · rw [abs_of_nonpos h0]; linarith
  have hcard : ((Finset.Ioc (2 ^ j) (2 * 2 ^ j)).card : ℝ) = ((2 ^ j : ℕ) : ℝ) := by
    rw [Nat.card_Ioc]; congr 1; omega
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), |lam n|
      ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), ((lam n + C) + C) := Finset.sum_le_sum hle
    _ = ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), (lam n + C) +
        C * ((Finset.Ioc (2 ^ j) (2 * 2 ^ j)).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ B * ((2 ^ j : ℕ) : ℝ) + C * ((2 ^ j : ℕ) : ℝ) := by rw [hcard]; linarith [hB _ hN]
    _ ≤ (B + C) * 2 ^ j * ((j : ℝ) + 1) := by
        push_cast
        have : (0 : ℝ) ≤ (B + C) * 2 ^ j := by positivity
        nlinarith

theorem tsum_one_div_rpow_eq_re_riemannZeta {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + s) = (riemannZeta (1 + s)).re := by
  have e : (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ ((1 : ℂ) + s)) =
      fun n : ℕ => ((1 / (n : ℝ) ^ (1 + s) : ℝ) : ℂ) := by
    funext n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast; ring
  rw [zeta_eq_tsum_one_div_nat_cpow (by simp; linarith), e, ← Complex.ofReal_tsum,
    Complex.ofReal_re]

theorem oddDirichlet_ge_of_ge {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {C : ℝ} (hC : 0 ≤ C)
    (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) {s : ℝ} (hs : 0 < s) :
    -C * (riemannZeta (1 + s)).re ≤ oddDirichlet lam s := by
  rw [← tsum_one_div_rpow_eq_re_riemannZeta hs, ← tsum_mul_left]
  have hsum1 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hsumF : Summable fun n : ℕ => (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s) := by
    refine Summable.of_norm_bounded (hsl (1 + s) (by linarith)) fun n => ?_
    rw [Real.norm_eq_abs]
    split_ifs
    · rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    · rw [zero_div, abs_zero]; positivity
  unfold oddDirichlet
  refine (hsum1.mul_left (-C)).tsum_le_tsum (fun n => ?_) hsumF
  have hp : 0 ≤ (n : ℝ) ^ (1 + s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  split_ifs with hn
  · rw [show -C * (1 / (n : ℝ) ^ (1 + s)) = -C / (n : ℝ) ^ (1 + s) by ring]
    exact div_le_div_of_nonneg_right (hlb n hn) hp
  · rw [zero_div]
    have : 0 ≤ 1 / (n : ℝ) ^ (1 + s) := by positivity
    nlinarith

theorem eventually_neg_le_of_ge {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {C : ℝ} (hC : 0 ≤ C)
    (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s) := by
  intro ε hε
  have hg : Tendsto (fun σ : ℝ => ((σ : ℂ) * riemannZeta (1 + σ)).re) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (Complex.continuous_re.tendsto (1 : ℂ)).comp tendsto_mul_riemannZeta_one_add
    rw [Complex.one_re] at h1
    exact h1
  have hδ : (0 : ℝ) < ε / (2 * C + 1) := by positivity
  filter_upwards [self_mem_nhdsWithin, hg.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with s hs h1 h2
  have hs' : 0 < s := hs
  have hF := oddDirichlet_ge_of_ge hsl hC hlb hs'
  rw [Complex.re_ofReal_mul] at h1
  have hz : s * (riemannZeta (1 + s)).re ≤ 2 := h1.le
  have k1 : s * (s * (-C * (riemannZeta (1 + s)).re)) ≤ s * (s * oddDirichlet lam s) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hs'.le) hs'.le
  have k2 : s * (s * (-C * (riemannZeta (1 + s)).re)) =
      -C * s * (s * (riemannZeta (1 + s)).re) := by ring
  have k3 : -C * s * 2 ≤ -C * s * (s * (riemannZeta (1 + s)).re) := by
    have : 0 ≤ C * s := by positivity
    nlinarith
  have k4 : C * s * 2 ≤ ε := by
    have h3 : s * (2 * C + 1) < ε := by rwa [lt_div_iff₀ (by positivity)] at h2
    nlinarith
  linarith

/-- **Even rigidity for weights bounded below.**  A weight system bounded below that is
Weil-positive on even tests at some pole weight is `Λ`, and RH holds. -/
theorem riemannHypothesis_of_weilPositiveEvenAt_of_ge {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) {C : ℝ} (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hlb' : ∀ n, 2 ≤ n → -max C 0 ≤ lam n := fun n hn =>
    (neg_le_neg (le_max_left C 0)).trans (hlb n hn)
  have hsl := fun σ (hσ : 1 < σ) => summable_abs_div_rpow_of_weilPositiveEvenAt_of_ge h hC hlb' hσ
  exact riemannHypothesis_of_weilPositiveEvenAt_of_abel h hsl (eventually_neg_le_of_ge hsl hC hlb')

/-- **Every even-positive weight system other than `Λ` is unbounded below.**  RH holds iff some
weight system bounded below is Weil-positive on even tests at some pole weight. -/
theorem riemannHypothesis_iff_exists_bddBelow_weilPositiveEvenAt :
    RiemannHypothesis ↔ ∃ (β C : ℝ) (lam : ℕ → ℝ), (∀ n, 2 ≤ n → -C ≤ lam n) ∧
      WeilPositiveEvenAt β lam := by
  constructor
  · intro hRH
    exact ⟨1, 0, fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      fun n _ => by simp [ArithmeticFunction.vonMangoldt_nonneg],
      weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩⟩
  · rintro ⟨β, C, lam, hlb, h⟩
    exact (riemannHypothesis_of_weilPositiveEvenAt_of_ge h hlb).1

end RHTower.EvenSector

end
