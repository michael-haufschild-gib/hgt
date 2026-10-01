import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.RHTower.LevinsonOddFiberFinal

/-!
# What Levinson's Littlewood budget counts

Let `G♯ = (s − 1)²(ζ + λζ')` be the entire Levinson detector (`levinsonGEntire`) and `Ψ` an entire
mollifier. Littlewood's lemma bounds the zeros of `G♯` in `[1/2, 4] × [T₁, T₂]`, weighted by
`1/2 − σ₀`, by the boundary functional of `G♯Ψ` on `[σ₀, d] × [T₁, T₂]`
(`levinsonGEntire_zeroMass_le_boundary`).

**Theorem** (`two_pi_mul_offLine_add_multiplicityDefect_le_levinsonBoundary`). Let `λ > 0` with
`λ(½ log(T₂/2π) + 1/20) < 1`, and let `100 ≤ T₁ < T₂` be unshadowed heights. Then

`2π(1/2 − σ₀) · (N_right(ξ) + Σ_{on-line zeros ρ} (m_ρ − 1)) ≤ boundary functional of G♯Ψ`,

where `N_right(ξ)` counts, with multiplicity, the zeros of `ξ` in `1/2 < Re s < 2`,
`T₁ < Im s < T₂`, and `m_ρ` is the order of an on-line zero `ρ` with `T₁ < Im ρ < T₂`.

**Proof.**
- Right of the line, `G♯` has exactly as many zeros as `ξ` (`exists_levinsonG_count_right`).
- At an on-line zero `ρ` of order `m`, `G♯ = a ξ + b ξ'` near `ρ`, with `a, b` analytic. Since `ξ'`
  vanishes to order `m − 1`, `G♯` vanishes to order at least `m − 1`
  (`toNat_analyticOrderAt_xi_le_levinsonGEntire_add_one`).
- The two families of zeros are disjoint and both lie in `[1/2, 4] × [T₁, T₂]`.

So, in this range of `λ`, Levinson's mean-square budget is a joint upper bound for the off-line
count and the on-line multiplicity defect. Simple on-line zeros cost nothing.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- At a zero `ρ` of `ξ` with `Re ρ > 0`, `ρ ≠ 1`, the detector `(s − 1)²(ζ + λζ')` vanishes to
order at least `ord_ρ ξ − 1`. -/
theorem toNat_analyticOrderAt_xi_le_levinsonGEntire_add_one {lam : ℂ} (hlam : lam ≠ 0)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ ≠ 1) (hξ : xi ρ = 0) :
    (analyticOrderAt xi ρ).toNat ≤ (analyticOrderAt (levinsonGEntire lam) ρ).toNat + 1 := by
  have hXA : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ trivial
  have hDA : AnalyticAt ℂ (deriv xi) ρ := analyticOnNhd_deriv_xi ρ trivial
  -- `ord ξ = ord ξ' + 1`
  have hord : analyticOrderAt (deriv xi) ρ + 1 = analyticOrderAt xi ρ := by
    have h := hXA.analyticOrderAt_deriv_add_one
    simpa [hξ] using h
  -- the local form `G♯ = a ξ + b ξ'`
  have hAA := analyticAt_archFactor_of_re_pos h0
  have hA0 := archFactor_ne_zero_of_re_pos h0 h1
  set k : ℂ → ℂ := fun s => (archFactor s)⁻¹ with hk
  have hkA : AnalyticAt ℂ k ρ := hAA.inv hA0
  set a : ℂ → ℂ := fun s => (s - 1) ^ 2 * (k s + lam * deriv k s) with ha
  set b : ℂ → ℂ := fun s => (s - 1) ^ 2 * (lam * k s) with hb
  have haA : AnalyticAt ℂ a ρ :=
    (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ 2) ρ).mul
      (hkA.add (analyticAt_const.mul hkA.deriv))
  have hbA : AnalyticAt ℂ b ρ :=
    (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ 2) ρ).mul (analyticAt_const.mul hkA)
  set U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hzeta : ∀ z ∈ U, riemannZeta z = k z * xi z := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; exact lt_irrefl 0 hz.1
    have hAz := archFactor_ne_zero_of_re_pos hz.1 hz.2
    rw [xi_eq_archFactor_mul_zeta hz0 hz.2 (Complex.Gammaℝ_ne_zero_of_re_pos hz.1), hk]
    field_simp
  have hev : levinsonGEntire lam =ᶠ[𝓝 ρ] a * xi + b * deriv xi := by
    filter_upwards [hUo.mem_nhds (show ρ ∈ U from ⟨h0, h1⟩)] with z hz
    have hevz : riemannZeta =ᶠ[𝓝 z] fun w => k w * xi w := by
      filter_upwards [hUo.mem_nhds hz] with w hw using hzeta w hw
    have hkz : DifferentiableAt ℂ k z :=
      ((analyticAt_archFactor_of_re_pos hz.1).inv (archFactor_ne_zero_of_re_pos hz.1 hz.2)).differentiableAt
    have hderiv : deriv riemannZeta z = deriv k z * xi z + k z * deriv xi z := by
      rw [hevz.deriv_eq]
      exact (hkz.hasDerivAt.mul (xi_differentiable z).hasDerivAt).deriv
    rw [levinsonGEntire_eq lam hz.2, levinsonG, hderiv, hzeta z hz]
    simp only [Pi.add_apply, Pi.mul_apply, ha, hb]
    ring
  -- order comparison
  have hlow : analyticOrderAt (deriv xi) ρ ≤ analyticOrderAt (levinsonGEntire lam) ρ := by
    rw [analyticOrderAt_congr hev]
    refine le_trans (le_min ?_ ?_) le_analyticOrderAt_add
    · rw [analyticOrderAt_mul haA hXA, ← hord]
      calc analyticOrderAt (deriv xi) ρ ≤ analyticOrderAt (deriv xi) ρ + 1 := le_self_add
        _ ≤ analyticOrderAt a ρ + (analyticOrderAt (deriv xi) ρ + 1) := le_add_self
    · rw [analyticOrderAt_mul hbA hDA]
      exact le_add_self
  have hGtop : analyticOrderAt (levinsonGEntire lam) ρ ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire_exists_ne_zero (analyticOnNhd_levinsonGEntire lam)
      (exists_levinsonGEntire_ne_zero hlam) ρ
  have hDtop : analyticOrderAt (deriv xi) ρ ≠ ⊤ := fun h => by
    have hXtop : analyticOrderAt xi ρ ≠ ⊤ :=
      DeBruijn.analyticOrderAt_ne_top_of_ne_zero xi_analyticOnNhd_univ
        (by simpa using xi_ne_zero_of_real 0) ρ
    rw [← hord, h, top_add] at hXtop
    exact hXtop rfl
  rw [← hord, ENat.toNat_add hDtop (by simp), ENat.toNat_one]
  exact Nat.add_le_add_right (ENat.toNat_le_toNat hlow hGtop) 1

/-- **Levinson's budget counts the off-line zeros and the on-line multiplicity defect.** -/
theorem two_pi_mul_offLine_add_multiplicityDefect_le_levinsonBoundary {lam T₁ T₂ σ₀ d : ℝ}
    (hlam : 0 < lam) (hlamT : lam * (Real.log (T₂ / (2 * Real.pi)) / 2 + 1 / 20) < 1)
    (h100 : 100 ≤ T₁) (hT : T₁ < T₂) (hu₁ : SpeiserUnshadowed T₁) (hu₂ : SpeiserUnshadowed T₂)
    {Ψ : ℂ → ℂ} (hΨ : AnalyticOnNhd ℂ Ψ Set.univ) (hΨne : ∃ z : ℂ, Ψ z ≠ 0)
    (hσ₀ : σ₀ < 1 / 2) (hd : 4 ≤ d)
    (hbot : ∀ x ∈ uIcc σ₀ d, levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) *
      Ψ ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc σ₀ d, levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) *
      Ψ ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0)
    (hrightne : ∀ t ∈ uIcc T₁ T₂, levinsonGEntire (lam : ℂ) ((d : ℂ) + (t : ℂ) * I) *
      Ψ ((d : ℂ) + (t : ℂ) * I) ≠ 0)
    (Z₀ Zon : Finset ℂ) (hZ₀ : ∀ w : ℂ, w ∈ Z₀ ↔ rightHalfWindow T₁ T₂ w ∧ xi w = 0)
    (hZon : ∀ w : ℂ, w ∈ Zon ↔ w.re = 1 / 2 ∧ T₁ < w.im ∧ w.im < T₂ ∧ xi w = 0) :
    2 * Real.pi * ((1 / 2 - σ₀) *
        ((∑ w ∈ Z₀, ((analyticOrderAt xi w).toNat : ℝ)) +
          ∑ w ∈ Zon, (((analyticOrderAt xi w).toNat : ℝ) - 1)))
      ≤ weightedLittlewoodBoundary (fun z => levinsonGEntire (lam : ℂ) z * Ψ z) σ₀ d T₁ T₂ := by
  classical
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  set G := levinsonGEntire (lam : ℂ) with hGdef
  have hGA := analyticOnNhd_levinsonGEntire (lam : ℂ)
  -- the zeros of `G♯` in `[1/2, 4] × [T₁, T₂]`
  have hfin0 := entire_zeros_closedRectangle_finite hGA (exists_levinsonGEntire_ne_zero hlamC)
    (((1 / 2 : ℝ) : ℂ) + T₁ * I) (((4 : ℝ) : ℂ) + T₂ * I)
  have hbox : (uIcc (((1 / 2 : ℝ) : ℂ) + T₁ * I).re (((4 : ℝ) : ℂ) + T₂ * I).re ×ℂ
      uIcc (((1 / 2 : ℝ) : ℂ) + T₁ * I).im (((4 : ℝ) : ℂ) + T₂ * I).im) =
      (uIcc (1 / 2 : ℝ) 4 ×ℂ uIcc T₁ T₂) := by
    simp
  rw [hbox] at hfin0
  set Z := hfin0.toFinset with hZdef
  have hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) 4 ×ℂ uIcc T₁ T₂) ∧ G z = 0 := by
    intro z; rw [hZdef, Set.Finite.mem_toFinset]; rfl
  have hmass := levinsonGEntire_zeroMass_le_boundary hlamC hΨ hΨne hσ₀ hd hT hbot htop
    hrightne Z hZ
  -- the right zeros
  obtain ⟨Z₁, Z₀', hZ₁, hZ₀', hcount⟩ :=
    exists_levinsonG_count_right hlam hlamT h100 hT hu₁ hu₂
  have hZ₀eq : Z₀' = Z₀ := by ext w; rw [hZ₀' w, hZ₀ w]
  rw [hZ₀eq] at hcount
  have hw1 : ∀ w : ℂ, T₁ < w.im → w ≠ 1 := fun w hw h => by
    rw [h, Complex.one_im] at hw; linarith
  have hmemR : ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 4 → T₁ ≤ w.im → w.im ≤ T₂ →
      w ∈ (uIcc (1 / 2 : ℝ) 4 ×ℂ uIcc T₁ T₂) := by
    intro w h1 h2 h3 h4
    rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le hT.le]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hsub₁ : Z₁ ⊆ Z := by
    intro w hw
    obtain ⟨hwin, hG0⟩ := (hZ₁ w).mp hw
    refine (hZ w).mpr ⟨hmemR w hwin.1.le (by linarith [hwin.2.1]) hwin.2.2.1.le hwin.2.2.2.le, ?_⟩
    exact (levinsonGEntire_eq_zero_iff _ (hw1 w hwin.2.2.1)).mpr hG0
  -- the on-line zeros where `G♯` vanishes
  set Zon' := Zon.filter (fun w => ((analyticOrderAt G w).toNat : ℝ) ≠ 0) with hZon'
  have hsubon : Zon' ⊆ Z := by
    intro w hw
    obtain ⟨hwZ, hne⟩ := Finset.mem_filter.mp hw
    obtain ⟨hre, h1, h2, -⟩ := (hZon w).mp hwZ
    have hne' : analyticOrderAt G w ≠ 0 := fun h => by simp [h] at hne
    refine (hZ w).mpr ⟨hmemR w hre.ge (by rw [hre]; norm_num) h1.le h2.le, ?_⟩
    exact ((analyticOrderAt_ne_zero).mp hne').2
  have hdisj : Disjoint Z₁ Zon' := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    have h1 := ((hZ₁ w).mp hw).1.1
    have h2 := ((hZon w).mp (Finset.mem_filter.mp hw').1).1
    linarith
  have hsumZ : (∑ w ∈ Z₁, ((analyticOrderAt G w).toNat : ℝ)) +
      ∑ w ∈ Zon', ((analyticOrderAt G w).toNat : ℝ) ≤
        ∑ w ∈ Z, ((analyticOrderAt G w).toNat : ℝ) := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hsub₁ hsubon)
      (fun _ _ _ => Nat.cast_nonneg _)
  have hon : (∑ w ∈ Zon, (((analyticOrderAt xi w).toNat : ℝ) - 1)) ≤
      ∑ w ∈ Zon', ((analyticOrderAt G w).toNat : ℝ) := by
    rw [hZon', Finset.sum_filter_ne_zero]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hre, h1, -, hxi⟩ := (hZon w).mp hw
    have h0 : 0 < w.re := by rw [hre]; norm_num
    have := toNat_analyticOrderAt_xi_le_levinsonGEntire_add_one hlamC h0 (hw1 w h1) hxi
    have hc : ((analyticOrderAt xi w).toNat : ℝ) ≤ ((analyticOrderAt G w).toNat : ℝ) + 1 := by
      exact_mod_cast this
    linarith
  have hright : (∑ w ∈ Z₀, ((analyticOrderAt xi w).toNat : ℝ)) =
      ∑ w ∈ Z₁, ((analyticOrderAt G w).toNat : ℝ) := by
    exact_mod_cast hcount.symm
  have htotal : (∑ w ∈ Z₀, ((analyticOrderAt xi w).toNat : ℝ)) +
      ∑ w ∈ Zon, (((analyticOrderAt xi w).toNat : ℝ) - 1) ≤
        ∑ w ∈ Z, ((analyticOrderAt G w).toNat : ℝ) := by
    rw [hright]; linarith
  have hσ : 0 ≤ 1 / 2 - σ₀ := by linarith
  calc 2 * Real.pi * ((1 / 2 - σ₀) *
        ((∑ w ∈ Z₀, ((analyticOrderAt xi w).toNat : ℝ)) +
          ∑ w ∈ Zon, (((analyticOrderAt xi w).toNat : ℝ) - 1)))
      ≤ 2 * Real.pi * ((1 / 2 - σ₀) * ∑ w ∈ Z, ((analyticOrderAt G w).toNat : ℝ)) := by
        gcongr
    _ ≤ _ := hmass

/-- `log(T/2π) ≥ 2` for `T ≥ 100`. -/
theorem two_le_log_div_two_pi {T : ℝ} (hT : 100 ≤ T) : 2 ≤ Real.log (T / (2 * Real.pi)) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he : Real.exp 2 < 8 := by
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_pos 1]
  have hπ := Real.pi_lt_d2
  rw [le_div_iff₀ (by positivity)]
  have h : Real.exp 2 * (2 * Real.pi) < 8 * (2 * 3.15) :=
    mul_lt_mul'' he (by linarith) (Real.exp_pos 2).le (by positivity)
  linarith

/-- **Off-line count and multiplicity defect from Levinson's mollified mean square.** With the
budget constants `C, K` of `exists_levinson_mollified_budget_le`: for `λ > 0` with
`λ(½ log(T₂/2π) + 1/20) < 1`, unshadowed `100 ≤ T₁ < T₂`, a Levinson mollifier `Ψ = Σ b_n n^{−s}`
and any upper bound `Msq` for `∫|(ζ + λζ')Ψ(σ₀ + it)|² dt`,

`2π(1/2 − σ₀)(N_right(ξ) + Σ_on (m_ρ − 1)) ≤ ½(T₂ − T₁) log(Msq/(T₂ − T₁)) + C + K(log T₂ + log Mb)`. -/
theorem exists_offLine_add_multiplicityDefect_le_of_mollified_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ lam : ℝ, 0 < lam →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 100 ≤ T₁ → T₁ < T₂ →
        lam * (Real.log (T₂ / (2 * Real.pi)) / 2 + 1 / 20) < 1 →
        SpeiserUnshadowed T₁ → SpeiserUnshadowed T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z₀ Zon : Finset ℂ, (∀ w : ℂ, w ∈ Z₀ ↔ rightHalfWindow T₁ T₂ w ∧ xi w = 0) →
        (∀ w : ℂ, w ∈ Zon ↔ w.re = 1 / 2 ∧ T₁ < w.im ∧ w.im < T₂ ∧ xi w = 0) →
        2 * Real.pi * ((1 / 2 - σ₀) *
            ((∑ w ∈ Z₀, ((analyticOrderAt xi w).toNat : ℝ)) +
              ∑ w ∈ Zon, (((analyticOrderAt xi w).toNat : ℝ) - 1)))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨C, K, hC, hK, hbudget⟩ := exists_levinson_mollified_budget_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro lam hlam b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h100 hT hlamT hu₁ hu₂
    hG1 hG2 hP1 hP2 hMsq Z₀ Zon hZ₀ hZon
  have hlog2 := two_le_log_div_two_pi (show 100 ≤ T₂ by linarith)
  have hlam1 : |lam| ≤ 1 := by rw [abs_of_pos hlam]; nlinarith
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ m ∈ s, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have h1mem : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hlamN : ‖((lam : ℝ) : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  set Ψ : ℂ → ℂ := edPoly b s with hΨdef
  set g : ℂ → ℂ := levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s with hgdef
  set F : ℂ → ℂ := fun z => levinsonGEntire ((lam : ℝ) : ℂ) z * Ψ z with hFdef
  have hΨana : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have hΨsmall : ∀ z : ℂ, 4 ≤ z.re → Ψ z ≠ 0 := by
    intro z hre h0
    have hd := norm_edPoly_sub_one_le_exp b hs h1mem hb1 hbn (by linarith : (2 : ℝ) ≤ z.re)
    have hEsmall : Real.exp (-(Real.log 2) * z.re) ≤ 1 / 16 := by
      rw [exp_neg_log_two_eq]
      have hle : ((2 : ℝ) ^ (4 : ℝ)) ≤ ((2 : ℝ) ^ z.re) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hre
      have h16 : ((2 : ℝ) ^ (4 : ℝ)) = 16 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      rw [h16] at hle
      have hpos : (0 : ℝ) < (2 : ℝ) ^ z.re := Real.rpow_pos_of_pos (by norm_num) _
      rw [inv_le_iff_one_le_mul₀ hpos]
      linarith
    rw [hΨdef] at h0
    rw [h0] at hd
    have hone : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [hone] at hd
    linarith
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨((15 : ℝ) : ℂ), hΨsmall _ (by simp; norm_num)⟩
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t => hΨsmall _ (by simp; norm_num)
  have hGeright : ∀ t : ℝ,
      levinsonGEntire ((lam : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun t =>
    levinsonGEntire_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hGright : ∀ t : ℝ,
      levinsonG ((lam : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun t =>
    levinsonG_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hFbot : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) * Ψ ((x : ℂ) + (T₁ : ℂ) * I)
        ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP1 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ (by linarith))]
    exact hG1 x hx
  have hFtop : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) * Ψ ((x : ℂ) + (T₂ : ℂ) * I)
        ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP2 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith))]
    exact hG2 x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂,
      levinsonGEntire ((lam : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        * Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => mul_ne_zero (hGeright t) (hΨright t)
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz =>
    ((analyticOnNhd_levinsonGEntire ((lam : ℝ) : ℂ)) z hz).mul (hΨana z hz)
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, mul_ne_zero (hGeright T₁) (hΨright T₁)⟩
  have hrectfin : {z ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) | F z = 0}.Finite := by
    have h := entire_zeros_closedRectangle_finite hFan hFne
      ((σ₀ : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
    have hre1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).re = σ₀ := by simp
    have him1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
    have hre2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).re = 15 / 2 := by simp
    have him2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).im = T₂ := by simp
    rwa [hre1, him1, hre2, him2] at h
  have hmemleft : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      ((σ₀ : ℂ) + (t : ℂ) * I) ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((σ₀ : ℂ) + (t : ℂ) * I).re = σ₀ := by simp
      rw [h]; exact left_mem_uIcc
    · have h : ((σ₀ : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [h]; exact ht
  have hgFzero : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      (g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 ↔ F ((σ₀ : ℂ) + (t : ℂ) * I) = 0) := by
    intro t ht
    rw [huIcct] at ht
    have hzne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := hne1 σ₀ t (by linarith [ht.1])
    have heq : F ((σ₀ : ℂ) + (t : ℂ) * I)
        = (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) := by
      simp only [hFdef, hgdef, levinsonMollifiedDetector]
      rw [levinsonGEntire_eq _ hzne]
      ring
    rw [heq, mul_eq_zero]
    have hgauge : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hzne)
    simp [hgauge]
  have hgfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    have hinj : Set.InjOn (fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} := by
      intro x _ y _ hxy
      simpa using congrArg Complex.im hxy
    refine Set.Finite.of_finite_image (Set.Finite.subset hrectfin ?_) hinj
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    exact ⟨hmemleft t ht, (hgFzero t ht).mp hz⟩
  have hgex : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsubset : Set.Ioo T₁ T₂ ⊆
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} := fun t ht =>
      ⟨by rw [huIcct]; exact Set.Ioo_subset_Icc_self ht, hall t ht⟩
    exact (Set.Ioo_infinite hT) (hgfin.subset hsubset)
  have hbud := hbudget lam hlam1 b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq
    hσ₀ hσ₀' (by linarith) hT hG1 hG2 hP1 hP2 hgfin hgex hMsq
  -- gauge cancellation
  have hUsub : (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} := by
    intro z hz hEq
    have him := (Complex.mem_reProdIm.mp hz).2
    rw [huIcct, hEq, Complex.one_im] at him
    linarith [him.1]
  have hcongrF : weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr isOpen_ne hUsub ?_
    intro z hz
    simp only [hFdef, hgdef, levinsonMollifiedDetector]
    rw [levinsonGEntire_eq _ hz]
    ring
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul hσ₀15 hT ?_ ?_ ?_ ?_ ?_ hgfin
    · intro hmem
      have him := (Complex.mem_reProdIm.mp hmem).2
      rw [huIcct, Complex.one_im] at him
      linarith [him.1]
    · intro z hz
      exact analyticAt_levinsonMollifiedDetector _ b hs (hUsub hz)
    · intro x hx
      rw [huIccx] at hx
      exact mul_ne_zero (hG1 x hx) (hP1 x hx)
    · intro x hx
      rw [huIccx] at hx
      exact mul_ne_zero (hG2 x hx) (hP2 x hx)
    · intro t _
      exact mul_ne_zero (hGright t) (hΨright t)
  have hdefect := two_pi_mul_offLine_add_multiplicityDefect_le_levinsonBoundary hlam hlamT h100 hT
    hu₁ hu₂ hΨana hΨne hσ₀' (by norm_num : (4 : ℝ) ≤ 15 / 2) hFbot hFtop hFright Z₀ Zon hZ₀ hZon
  rw [hcongrF, hgaugefree] at hdefect
  exact hdefect.trans hbud

end

end RHTower
