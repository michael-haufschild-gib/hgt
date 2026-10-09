import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw

/-!
# Critical multiplicities and the logarithmic growth of the Möbius Hilbert form

Let `E_N = Σ_{m,n ≤ N} μ(m)μ(n)/(m+n)`.  If `ζ` vanishes to order at least `m` at a point `ρ` with
`Re ρ = ½`, then for every natural `k` with `k + 1 < 2m`

  `E_N ≤ c (log(N+1))^k + C` fails for every `c, C`

(`not_forall_hilbert_le_log_pow_of_analyticOrderAt`).  Equivalently, a bound
`E_N = O((log N)^k)` caps the order of every critical zero at `(k + 1)/2`
(`two_mul_le_of_hilbert_le_log_pow`); `k = 1` is the corpus simplicity statement
`deriv_riemannZeta_ne_zero_of_hilbert_log`.  At the threshold `k = 2m − 1` the bound fails for all
small `c` (`exists_pos_forall_not_hilbert_le_log_pow_of_analyticOrderAt`): `E_N = Ω((log N)^{2m−1})`.

**Proof.**  Since `(log(N+1))^k ≤ k! a^{−k}(N+1)^a`, the bound gives `E_N ≤ C_a(N+1)^a` for every
`a > 0` with `C_a ≍ a^{−k}`.  The sharp tail comparison and the layer cake by parts
(`intervalIntegral_sq_pencil_le_of_hilbert_power`, `intervalIntegral_rpow_mul_le_of_tail_rpow`)
with `a = r/2` give `∫|Γ/ζ|²(½ + r + it) dt ≤ A r^{−k} + B` (Fatou and Plancherel).  Near `ρ`,
`ζ(s) = (s − ρ)^n p(s)` with `n ≥ m`, so `|Γ/ζ| ≥ c₀ r^{−m}` on the window `|t − Im ρ| ≤ r` of the
line `Re s = ½ + r` (`exists_vertical_window_floor_pow_of_canonical_identity`), whose energy is
`≥ 2c₀² r^{1−2m}`.  As `r → 0` this exceeds `A r^{−k} + B` because `2m − 1 > k`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The explicit form of `exists_forall_energy_le_of_hilbert_power`: a power bound
`E_N(1) ≤ C(N+1)^a` gives `E_N(r) ≤ K + (r − 1)K/(r − 1 − p) + 4·2^{−r}Γ(r)` uniformly in `N`, where
`p = (1 + 1/m)a < r − 1` and `K = 2C·3^a + 8(m!)²`. -/
theorem finiteMobiusGammaHankelEnergy_le_of_hilbert_power {C a r : ℝ} (hC0 : 0 ≤ C) (ha : 0 ≤ a)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ a)
    (m : ℕ) (hm : 1 ≤ m) (hr : (1 + 1 / (m : ℝ)) * a < r - 1) (N : ℕ) :
    finiteMobiusGammaHankelEnergy N r ≤
      (2 * C * 3 ^ a + 8 * (m.factorial : ℝ) ^ 2) +
        (r - 1) * (2 * C * 3 ^ a + 8 * (m.factorial : ℝ) ^ 2) / (r - 1 - (1 + 1 / (m : ℝ)) * a) +
        4 * ((1 / 2) ^ r * Real.Gamma r) := by
  set p : ℝ := (1 + 1 / (m : ℝ)) * a with hpdef
  have hp : 0 ≤ p := by positivity
  have hr1 : 0 < r - 1 := lt_of_le_of_lt hp hr
  have hpos : 0 < r := by linarith
  set K : ℝ := 2 * C * 3 ^ a + 8 * (m.factorial : ℝ) ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  have hInt := integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N hpos
  rw [← integral_finiteMobiusLaplacePencil_sq N hpos,
    ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hfar := setIntegral_Ioi_one_rpow_mul_sq_pencil_le N hpos
  have hcont : Continuous fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2 :=
    (continuous_finiteMobiusLaplacePencil N).pow 2
  have hnear : ∫ x in Ioc (0 : ℝ) 1, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      K + (r - 1) * K / (r - 1 - p) := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    apply le_of_forall_pos_le_add
    intro δ hδ
    set ε : ℝ := min 1 (δ / ((N : ℝ) ^ 2 + 1)) with hεdef
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεδ : ε * ((N : ℝ) ^ 2 + 1) ≤ δ := by
      have := min_le_right 1 (δ / ((N : ℝ) ^ 2 + 1))
      rw [← hεdef] at this
      calc ε * ((N : ℝ) ^ 2 + 1) ≤ δ / ((N : ℝ) ^ 2 + 1) * ((N : ℝ) ^ 2 + 1) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = δ := by field_simp
    have hfcont : ContinuousOn (fun x : ℝ => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2)
        (uIcc 0 1) := fun x _ =>
      ((Real.continuousAt_rpow_const _ _ (Or.inr hr1.le)).mul hcont.continuousAt).continuousWithinAt
    have hi1 : IntervalIntegrable (fun x : ℝ => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2)
        volume 0 ε :=
      (hfcont.mono (uIcc_subset_uIcc (by simp) (by simp [hε0.le, hε1]))).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2)
        volume ε 1 :=
      (hfcont.mono (uIcc_subset_uIcc (by simp [hε0.le, hε1]) (by simp))).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hsmall : ∫ x in (0 : ℝ)..ε, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
        ε * ((N : ℝ) ^ 2 + 1) := by
      have hb : ∀ x ∈ Icc (0 : ℝ) ε, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
          (N : ℝ) ^ 2 + 1 := by
        intro x hx
        have hx1 : x ≤ 1 := hx.2.trans hε1
        have hpw : x ^ (r - 1) ≤ 1 := Real.rpow_le_one hx.1 hx1 hr1.le
        have hp0 : 0 ≤ x ^ (r - 1) := Real.rpow_nonneg hx.1 _
        have hF := abs_finiteMobiusLaplacePencil_le_card N hx.1
        have hF2 : finiteMobiusLaplacePencil N x ^ 2 ≤ (N : ℝ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hF 2
        nlinarith [sq_nonneg (finiteMobiusLaplacePencil N x)]
      have := intervalIntegral.integral_mono_on hε0.le hi1 intervalIntegrable_const hb
      rw [intervalIntegral.integral_const] at this
      simpa using this
    have hlayer := intervalIntegral_rpow_mul_le_of_tail_rpow hcont hK hp hr hε0 hε1
      (fun y hy => intervalIntegral_sq_pencil_le_of_hilbert_power hC0 ha hH m hm
        (lt_of_lt_of_le hε0 hy.1) hy.2 N)
    linarith
  linarith

/-- **Logarithmic powers give quantitative line energies.**  If `E_N ≤ c(log(N+1))^k + C` for
all `N`, then there is `B ≥ 0` with `E_N(1 + 2r) ≤ 18·max(c, 0)·k!·2^k r^{−k} + B` for all `N` and
`0 < r ≤ 1/2`. -/
theorem exists_energy_le_of_hilbert_le_log_pow {c C : ℝ} {k : ℕ}
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) ^ k + C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ N : ℕ,
      finiteMobiusGammaHankelEnergy N (1 + 2 * r) ≤
        18 * max c 0 * k.factorial * 2 ^ k * (r⁻¹) ^ k + B := by
  set c' : ℝ := max c 0 with hc'
  set C' : ℝ := max C 0 with hC'
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  -- power bounds with explicit constants
  have hpow : ∀ a : ℝ, 0 < a → ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤
      (c' * k.factorial * (a⁻¹) ^ k + C') * ((N : ℝ) + 1) ^ a := by
    intro a ha N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
    set L : ℝ := Real.log ((N : ℝ) + 1) with hL
    have hL0 : 0 ≤ L := Real.log_nonneg hN1
    have hexp := Real.pow_div_factorial_le_exp (a * L) (by positivity) k
    have hNa : Real.exp (a * L) = ((N : ℝ) + 1) ^ a := by
      rw [Real.rpow_def_of_pos (by linarith), mul_comm]
    rw [hNa, div_le_iff₀ (by positivity)] at hexp
    have h1 : L ^ k ≤ k.factorial * (a⁻¹) ^ k * ((N : ℝ) + 1) ^ a := by
      calc L ^ k = (a⁻¹) ^ k * (a * L) ^ k := by
            rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha.ne', one_pow, one_mul]
        _ ≤ (a⁻¹) ^ k * (((N : ℝ) + 1) ^ a * k.factorial) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = k.factorial * (a⁻¹) ^ k * ((N : ℝ) + 1) ^ a := by ring
    have h2 : 1 ≤ ((N : ℝ) + 1) ^ a := Real.one_le_rpow hN1 ha.le
    have hLk : 0 ≤ L ^ k := pow_nonneg hL0 k
    have h3 : c * L ^ k ≤ c' * L ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) hLk
    have h4 : c' * L ^ k ≤ c' * (k.factorial * (a⁻¹) ^ k * ((N : ℝ) + 1) ^ a) :=
      mul_le_mul_of_nonneg_left h1 hc'0
    have h5 : C ≤ C' * ((N : ℝ) + 1) ^ a := by
      have := mul_le_mul_of_nonneg_left h2 hC'0
      linarith [le_max_left C 0]
    have := hH N
    have e : (c' * k.factorial * (a⁻¹) ^ k + C') * ((N : ℝ) + 1) ^ a =
        c' * (k.factorial * (a⁻¹) ^ k * ((N : ℝ) + 1) ^ a) + C' * ((N : ℝ) + 1) ^ a := by ring
    linarith
  refine ⟨18 * C' + 28, by positivity, fun r hr hr2 N => ?_⟩
  set a : ℝ := r / 2 with ha
  have ha0 : 0 < a := by positivity
  set Ca : ℝ := c' * k.factorial * (a⁻¹) ^ k + C' with hCa
  have hCa0 : 0 ≤ Ca := by positivity
  have hp : (1 + 1 / ((1 : ℕ) : ℝ)) * a = r := by rw [ha]; push_cast; ring
  have hlt : (1 + 1 / ((1 : ℕ) : ℝ)) * a < (1 + 2 * r) - 1 := by rw [hp]; linarith
  have hE := finiteMobiusGammaHankelEnergy_le_of_hilbert_power hCa0 ha0.le (hpow a ha0) 1 le_rfl
    hlt N
  rw [hp] at hE
  simp only [Nat.factorial_one, Nat.cast_one, one_pow, mul_one] at hE
  have hR : (1 + 2 * r) - 1 - r = r := by ring
  rw [hR] at hE
  have hfrac : ((1 + 2 * r) - 1) * (2 * Ca * 3 ^ a + 8) / r = 2 * (2 * Ca * 3 ^ a + 8) := by
    field_simp; ring
  rw [hfrac] at hE
  have h3a : (3 : ℝ) ^ a ≤ 3 := by
    calc (3 : ℝ) ^ a ≤ 3 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [ha]; linarith)
      _ = 3 := Real.rpow_one 3
  have hGam : 4 * ((1 / 2) ^ (1 + 2 * r) * Real.Gamma (1 + 2 * r)) ≤ 4 := by
    have hG := gamma_le_one_of_mem_Icc (by linarith : (1 : ℝ) ≤ 1 + 2 * r) (by linarith)
    have hG0 : 0 ≤ Real.Gamma (1 + 2 * r) := (Real.Gamma_pos_of_pos (by linarith)).le
    have hh : (1 / 2 : ℝ) ^ (1 + 2 * r) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
    have hh0 : 0 ≤ (1 / 2 : ℝ) ^ (1 + 2 * r) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hainv : (a⁻¹) ^ k = 2 ^ k * (r⁻¹) ^ k := by
    rw [ha, inv_div, ← mul_pow]; congr 1
  have hK : 2 * Ca * 3 ^ a + 8 ≤ 6 * c' * k.factorial * 2 ^ k * (r⁻¹) ^ k + 6 * C' + 8 := by
    have h1 : 2 * Ca * 3 ^ a ≤ 2 * Ca * 3 := mul_le_mul_of_nonneg_left h3a (by positivity)
    have e : 2 * Ca * 3 = 6 * c' * k.factorial * 2 ^ k * (r⁻¹) ^ k + 6 * C' := by
      rw [hCa, hainv]; ring
    linarith
  have e2 : 18 * c' * k.factorial * 2 ^ k * (r⁻¹) ^ k + (18 * C' + 28) =
      3 * (6 * c' * k.factorial * 2 ^ k * (r⁻¹) ^ k + 6 * C' + 8) + 4 := by ring
  rw [show 18 * c' * k.factorial * 2 ^ k * (r⁻¹) ^ k = 18 * c' * k.factorial * 2 ^ k *
    (r⁻¹) ^ k from rfl]
  linarith

/-- **A floor of order `m` at a boundary zero.**  If `ζ` vanishes to order at least `m` at `ρ` with
`Re ρ = σ ∈ (0, 1)` and `G·(s − 1)ζ = Γ(s)(s − 1)` on `Re s > σ`, then `‖G‖ ≥ c/r^m` on the vertical
window `|t − Im ρ| ≤ r` of the line `Re s = σ + r`, for all small `r > 0`. -/
theorem exists_vertical_window_floor_pow_of_canonical_identity
    {sigma : ℝ} {rho : ℂ} {m : ℕ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hrho : rho.re = sigma)
    (hord : (m : ℕ∞) ≤ analyticOrderAt riemannZeta rho) :
    ∃ c > 0, ∃ delta > 0, ∀ G : ℂ → ℂ, (∀ z : ℂ, sigma < z.re →
      G z * zetaResidueUnit z = Complex.Gamma z * (z - 1)) →
      ∀ r : ℝ, 0 < r → r < delta → ∀ t : ℝ, |t - rho.im| ≤ r →
        c / r ^ m ≤ ‖G (((sigma + r : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
    linarith
  have hrhoPos : 0 < rho.re := by rw [hrho]; exact hsigma
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta rho := analyticOn_riemannZeta rho hrhoOne
  have horderFinite : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (x := 2) (by simp) (by simpa using hrhoOne)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)))]
    exact ENat.zero_ne_top
  set n : ℕ := (analyticOrderAt riemannZeta rho).toNat with hndef
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta rho := ENat.coe_toNat horderFinite
  have hmn : m ≤ n := by
    have : (m : ℕ∞) ≤ (n : ℕ∞) := hncoe ▸ hord
    exact_mod_cast this
  obtain ⟨p, hp, hpzero, hfactor⟩ :=
    (hzetaAnalytic.analyticOrderAt_eq_natCast).mp hncoe.symm
  have hnotGammaPole : ∀ j : ℕ, rho ≠ -(j : ℂ) := by
    intro j h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    rw [hrho] at hre
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  let q : ℂ → ℂ := fun z => Complex.Gamma z / p z
  have hqcont : ContinuousAt q rho :=
    (Complex.continuousAt_Gamma rho hnotGammaPole).div hp.continuousAt hpzero
  have hqzero : q rho ≠ 0 := div_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhoPos) hpzero
  have hqpos : 0 < ‖q rho‖ := norm_pos_iff.mpr hqzero
  have hqfloor : ∀ᶠ z : ℂ in 𝓝 rho, ‖q rho‖ / 2 < ‖q z‖ :=
    hqcont.norm.eventually_const_lt (by linarith)
  have hpne : ∀ᶠ z : ℂ in 𝓝 rho, p z ≠ 0 :=
    hp.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds hpzero)
  have hlocal : ∀ᶠ z : ℂ in 𝓝 rho,
      riemannZeta z = (z - rho) ^ n * p z ∧ p z ≠ 0 ∧ ‖q rho‖ / 2 ≤ ‖q z‖ := by
    filter_upwards [hfactor, hpne, hqfloor] with z hz hpz hqz
    exact ⟨by simpa [smul_eq_mul] using hz, hpz, hqz.le⟩
  obtain ⟨eps, heps, hepsLocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  let delta : ℝ := min (eps / 2) (min ((1 - sigma) / 2) (1 / 2))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    have : 0 < 1 - sigma := by linarith
    positivity
  refine ⟨‖q rho‖ / 2 ^ (m + 1), by positivity, delta, hdelta, ?_⟩
  intro G hidentity r hr hrdelta t ht
  let z : ℂ := ((sigma + r : ℝ) : ℂ) + (t : ℂ) * I
  have hzre : z.re = sigma + r := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hrEps : 2 * r < eps := by
    have hle : delta ≤ eps / 2 := min_le_left _ _
    nlinarith
  have hrOneSub : r < (1 - sigma) / 2 := by
    have hle : delta ≤ (1 - sigma) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    exact hrdelta.trans_le hle
  have hrHalf : r < 1 / 2 := by
    have hle : delta ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    exact hrdelta.trans_le hle
  have hnorm : ‖z - rho‖ ≤ 2 * r := by
    calc ‖z - rho‖ ≤ |(z - rho).re| + |(z - rho).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = r + |t - rho.im| := by simp [hzre, hzim, hrho, abs_of_pos hr]
      _ ≤ 2 * r := by linarith
  have hzdist : dist z rho < eps := by
    rw [Complex.dist_eq]
    exact hnorm.trans_lt hrEps
  obtain ⟨hfactorz, hpnez, hqfloorz⟩ := hepsLocal hzdist
  have hzright : sigma < z.re := by rw [hzre]; linarith
  have hzone : z ≠ 1 := by
    intro hz1
    have hre := congrArg Complex.re hz1
    rw [hzre] at hre
    simp only [one_re] at hre
    nlinarith
  have hcanonical := hidentity z hzright
  simp only [zetaResidueUnit, Function.update_of_ne hzone] at hcanonical
  have hcancel : G z * riemannZeta z = Complex.Gamma z := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hzone)
    calc (G z * riemannZeta z) * (z - 1) = G z * ((z - 1) * riemannZeta z) := by ring
      _ = Complex.Gamma z * (z - 1) := hcanonical
  have hscaled : G z * (z - rho) ^ n = q z := by
    apply (eq_div_iff hpnez).2
    calc (G z * (z - rho) ^ n) * p z = G z * ((z - rho) ^ n * p z) := by ring
      _ = G z * riemannZeta z := by rw [hfactorz]
      _ = Complex.Gamma z := hcancel
  have hnormOne : ‖z - rho‖ ≤ 1 := by nlinarith
  have hnormPow : ‖z - rho‖ ^ n ≤ (2 * r) ^ m := by
    calc ‖z - rho‖ ^ n ≤ ‖z - rho‖ ^ m := pow_le_pow_of_le_one (norm_nonneg _) hnormOne hmn
      _ ≤ (2 * r) ^ m := pow_le_pow_left₀ (norm_nonneg _) hnorm m
  have hprod : ‖q rho‖ / 2 ≤ ‖G z‖ * (2 * r) ^ m := by
    calc ‖q rho‖ / 2 ≤ ‖q z‖ := hqfloorz
      _ = ‖G z‖ * ‖z - rho‖ ^ n := by rw [← hscaled, norm_mul, norm_pow]
      _ ≤ ‖G z‖ * (2 * r) ^ m := mul_le_mul_of_nonneg_left hnormPow (norm_nonneg _)
  change ‖q rho‖ / 2 ^ (m + 1) / r ^ m ≤ ‖G z‖
  have hrm : 0 < r ^ m := pow_pos hr m
  rw [div_div, div_le_iff₀ (by positivity)]
  have e : (2 * r) ^ m = 2 ^ m * r ^ m := mul_pow 2 r m
  rw [e] at hprod
  have e2 : ‖G z‖ * (2 ^ (m + 1) * r ^ m) = 2 * (‖G z‖ * (2 ^ m * r ^ m)) := by ring
  rw [e2]
  linarith

/-- **The line-energy floor at a critical zero of order `m`.**  There are `c₀, δ > 0` such that,
whenever the Möbius source is square integrable on every line `Re s = ½ + r`, `0 < r ≤ ¼`,
`2c₀² ≤ 2π r^{2m−1} ∫ |source(½ + r)|²` for all `0 < r < δ`, `r ≤ ¼`. -/
theorem exists_sq_le_pow_mul_line_energy_of_analyticOrderAt {ρ : ℂ} (hre : ρ.re = 1 / 2)
    {m : ℕ} (hm1 : 1 ≤ m) (hord : (m : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ c₀ > 0, ∃ δ > 0, (∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
        MemLp (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) 2 volume) →
      ∀ r : ℝ, 0 < r → r < δ → r ≤ 1 / 4 →
        2 * c₀ ^ 2 ≤ 2 * Real.pi * (r ^ (2 * m - 1) *
          ∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2) := by
  obtain ⟨c₀, hc₀, δ, hδ, hfloor⟩ := exists_vertical_window_floor_pow_of_canonical_identity
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hre hord
  refine ⟨c₀, hc₀, δ, hδ, fun hmem r hr hrδ hr4 => ?_⟩
  have hid : ∀ z : ℂ, 1 / 2 < z.re →
      mellin mobiusDiscreteLaplaceTransform z * zetaResidueUnit z = Complex.Gamma z * (z - 1) := by
    intro z hz
    set r' : ℝ := min ((z.re - 1 / 2) / 2) (1 / 4) with hr'def
    have hr' : 0 < r' := lt_min (by linarith) (by norm_num)
    have hr'4 : r' ≤ 1 / 4 := min_le_right _ _
    have hrz : 1 / 2 + r' < z.re := by
      have := min_le_left ((z.re - 1 / 2) / 2) (1 / 4)
      linarith
    exact mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base
      (by linarith) (hmem r' hr' hr'4) z hrz
  have hbase := hmem (r / 2) (half_pos hr) (by linarith)
  have h2 := hmem r hr hr4
  have h1 : Integrable (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) := by
    have := integrable_mobiusLaplaceLogMellinLineSource_of_base hbase (half_pos hr)
    rwa [show 1 / 2 + r / 2 + r / 2 = 1 / 2 + r by ring] at this
  have hlineInt := integrable_norm_sq_mellin_line_of_logMellinLineSource h1 h2
  have hPl := integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_eq h1 h2
  have hrm1 : 0 < r ^ (m - 1) := pow_pos hr _
  have hpowm : r ^ m = r ^ (m - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hm1]
  have hwin : ∀ t : ℝ, |t - ρ.im| ≤ r → (c₀ / r ^ (m - 1)) / r ≤
      ‖mellin mobiusDiscreteLaplaceTransform (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    intro t ht
    have := hfloor _ hid r hr hrδ t ht
    rwa [hpowm, ← div_div] at this
  have hlower := integral_norm_sq_ge_two_mul_sq_div_of_window_floor hr
    (div_nonneg hc₀.le hrm1.le) hlineInt hwin
  rw [hPl] at hlower
  have hpw : r ^ (2 * m - 1) = (r ^ (m - 1)) ^ 2 * r := by
    rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, pow_succ, pow_mul']
  have hX : 2 * (c₀ / r ^ (m - 1)) ^ 2 / r * r ^ (2 * m - 1) = 2 * c₀ ^ 2 := by
    rw [hpw]
    field_simp
  have h := mul_le_mul_of_nonneg_right hlower (by positivity : (0 : ℝ) ≤ r ^ (2 * m - 1))
  rw [hX] at h
  linarith

/-- **Critical multiplicity forces logarithmic growth of the Möbius Hilbert form.**  If `ζ` vanishes
to order at least `m` at `ρ` with `Re ρ = ½`, then for every `k` with `k + 1 < 2m` no bound
`Σ_{m',n ≤ N} μ(m')μ(n)/(m'+n) ≤ c(log(N+1))^k + C` holds for all `N`. -/
theorem not_forall_hilbert_le_log_pow_of_analyticOrderAt {ρ : ℂ} (hre : ρ.re = 1 / 2)
    {m k : ℕ} (hord : (m : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) (hk : k + 1 < 2 * m)
    (c C : ℝ) :
    ¬ ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) ^ k + C := by
  intro hH
  have hm1 : 1 ≤ m := by omega
  obtain ⟨c₀, hc₀, δ, hδ, hcore⟩ := exists_sq_le_pow_mul_line_energy_of_analyticOrderAt hre hm1 hord
  obtain ⟨B, hB0, hE⟩ := exists_energy_le_of_hilbert_le_log_pow hH
  set A : ℝ := 18 * max c 0 * k.factorial * 2 ^ k with hA
  have hA0 : 0 ≤ A := by
    have := le_max_right c 0
    positivity
  have hline : ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      MemLp (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) 2 volume ∧
        (∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2) ≤ A * (r⁻¹) ^ k + B := by
    intro r hr hr4
    apply memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
      (by linarith)
    intro N
    rw [show 2 * (1 / 2 + r) = 1 + 2 * r by ring]
    exact hE r hr (by linarith) N
  have hpi : 0 < Real.pi := Real.pi_pos
  set r : ℝ := min (δ / 2) (min (1 / 4) (c₀ ^ 2 / (2 * Real.pi * (A + B) + 1))) with hrdef
  have hr : 0 < r := lt_min (by linarith) (lt_min (by norm_num) (by positivity))
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr4 : r ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r ≤ c₀ ^ 2 / (2 * Real.pi * (A + B) + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hr1 : r ≤ 1 := by linarith
  have hchain := hcore (fun r hr hr4 => (hline r hr hr4).1) r hr hrδ hr4
  have hint := (hline r hr hr4).2
  -- `r^{2m−1}(A r^{−k} + B) = A r^j + B r^{2m−1} ≤ (A + B) r`
  set j : ℕ := 2 * m - 1 - k with hj
  have hj1 : 1 ≤ j := by omega
  have hsplit : r ^ (2 * m - 1) = r ^ k * r ^ j := by
    rw [← pow_add]; congr 1; omega
  have hY : r ^ (2 * m - 1) * (A * (r⁻¹) ^ k + B) = A * r ^ j + B * r ^ (2 * m - 1) := by
    have hinv : (r⁻¹) ^ k * r ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    rw [hsplit]
    linear_combination (A * r ^ j) * hinv
  have hrj : r ^ j ≤ r := pow_le_of_le_one hr.le hr1 (by omega)
  have hr2m : r ^ (2 * m - 1) ≤ r := pow_le_of_le_one hr.le hr1 (by omega)
  have hupper : r ^ (2 * m - 1) * ∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2 ≤
      (A + B) * r := by
    calc r ^ (2 * m - 1) * ∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2
        ≤ r ^ (2 * m - 1) * (A * (r⁻¹) ^ k + B) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = A * r ^ j + B * r ^ (2 * m - 1) := hY
      _ ≤ A * r + B * r := add_le_add (mul_le_mul_of_nonneg_left hrj hA0)
          (mul_le_mul_of_nonneg_left hr2m hB0)
      _ = (A + B) * r := by ring
  have hsmall : 2 * Real.pi * ((A + B) * r) < c₀ ^ 2 := by
    have hden : 0 < 2 * Real.pi * (A + B) + 1 := by positivity
    have hmul : r * (2 * Real.pi * (A + B) + 1) ≤ c₀ ^ 2 := by
      rwa [le_div_iff₀ hden] at hrc
    nlinarith
  have := mul_le_mul_of_nonneg_left hupper (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  nlinarith [sq_pos_of_pos hc₀]

/-- **The sharp logarithmic exponent.**  If `ζ` vanishes to order at least `m ≥ 1` at `ρ` with
`Re ρ = ½`, there is `c₁ > 0` such that no bound
`Σ_{m',n ≤ N} μ(m')μ(n)/(m'+n) ≤ c(log(N+1))^{2m−1} + C` with `c < c₁` holds for all `N`:
`E_N = Ω((log N)^{2m−1})`. -/
theorem exists_pos_forall_not_hilbert_le_log_pow_of_analyticOrderAt {ρ : ℂ} (hre : ρ.re = 1 / 2)
    {m : ℕ} (hm1 : 1 ≤ m) (hord : (m : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ c₁ > 0, ∀ c : ℝ, c < c₁ → ∀ C : ℝ,
      ¬ ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤
        c * Real.log ((N : ℝ) + 1) ^ (2 * m - 1) + C := by
  obtain ⟨c₀, hc₀, δ, hδ, hcore⟩ := exists_sq_le_pow_mul_line_energy_of_analyticOrderAt hre hm1 hord
  have hpi : 0 < Real.pi := Real.pi_pos
  set K : ℝ := 18 * ((2 * m - 1).factorial : ℝ) * 2 ^ (2 * m - 1) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨c₀ ^ 2 / (2 * Real.pi * K), by positivity, fun c hc C hH => ?_⟩
  obtain ⟨B, hB0, hE⟩ := exists_energy_le_of_hilbert_le_log_pow hH
  set A : ℝ := 18 * max c 0 * ((2 * m - 1).factorial : ℝ) * 2 ^ (2 * m - 1) with hA
  have hAK : A = max c 0 * K := by rw [hA, hK]; ring
  have hA0 : 0 ≤ A := by rw [hAK]; exact mul_nonneg (le_max_right _ _) hK0.le
  have hAlt : 2 * Real.pi * A < c₀ ^ 2 := by
    have hmax : max c 0 < c₀ ^ 2 / (2 * Real.pi * K) := max_lt hc (by positivity)
    rw [hAK]
    rw [lt_div_iff₀ (by positivity)] at hmax
    linarith
  have hline : ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      MemLp (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) 2 volume ∧
        (∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2) ≤
          A * (r⁻¹) ^ (2 * m - 1) + B := by
    intro r hr hr4
    apply memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
      (by linarith)
    intro N
    rw [show 2 * (1 / 2 + r) = 1 + 2 * r by ring]
    exact hE r hr (by linarith) N
  set gap : ℝ := c₀ ^ 2 - 2 * Real.pi * A with hgap
  have hgap0 : 0 < gap := by linarith
  set r : ℝ := min (δ / 2) (min (1 / 4) (gap / (2 * Real.pi * B + 1))) with hrdef
  have hr : 0 < r := lt_min (by linarith) (lt_min (by norm_num) (by positivity))
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr4 : r ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r ≤ gap / (2 * Real.pi * B + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hr1 : r ≤ 1 := by linarith
  have hchain := hcore (fun r hr hr4 => (hline r hr hr4).1) r hr hrδ hr4
  have hint := (hline r hr hr4).2
  have hY : r ^ (2 * m - 1) * (A * (r⁻¹) ^ (2 * m - 1) + B) = A + B * r ^ (2 * m - 1) := by
    rw [mul_add, mul_comm A, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul,
      mul_comm (r ^ (2 * m - 1)) B]
  have hr2m : r ^ (2 * m - 1) ≤ r := pow_le_of_le_one hr.le hr1 (by omega)
  have hupper : r ^ (2 * m - 1) * ∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2 ≤
      A + B * r := by
    calc r ^ (2 * m - 1) * ∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2
        ≤ r ^ (2 * m - 1) * (A * (r⁻¹) ^ (2 * m - 1) + B) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = A + B * r ^ (2 * m - 1) := hY
      _ ≤ A + B * r := by gcongr
  have hsmall : 2 * Real.pi * (B * r) < gap := by
    have hden : 0 < 2 * Real.pi * B + 1 := by positivity
    have hmul : r * (2 * Real.pi * B + 1) ≤ gap := by
      rwa [le_div_iff₀ hden] at hrc
    nlinarith
  have := mul_le_mul_of_nonneg_left hupper (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  nlinarith [sq_pos_of_pos hc₀]

/-- **Logarithmic Hilbert growth caps critical multiplicities.**  If
`Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) ≤ c(log(N+1))^k + C` for all `N`, then every order `m` of vanishing of
`ζ` at a point of the critical line satisfies `2m ≤ k + 1`. -/
theorem two_mul_le_of_hilbert_le_log_pow {c C : ℝ} {k : ℕ}
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) ^ k + C)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) {m : ℕ} (hord : (m : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    2 * m ≤ k + 1 := by
  by_contra h
  exact not_forall_hilbert_le_log_pow_of_analyticOrderAt hre hord (by omega) c C hH

end RHTower
