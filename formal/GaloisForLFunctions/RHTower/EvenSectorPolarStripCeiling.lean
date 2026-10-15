import GaloisForLFunctions.RHTower.EvenSectorPoleFreeNodeTests
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeLogDensity

/-!
# Even pole-free positivity on strip functions, resonators and the log-density ceiling

Let `lam` be Weil-positive on even compactly supported `C²` tests with `f̂(i/2) = 0`
(`WeilPositiveEvenPolar`), and let `|lam(n)| ≤ C √n (1 + log n)`.  No pole weight is assumed.

**Theorem** (`archPoleEnergy_sub_atomPairing_nonneg_of_polar`).  For every even `C²` test `F` whose
values and derivative decay like `e^{−b|x|}`, `b > 1`, and with `∫ F(u) e^{−u/2} du = 0`, the
pole-and-archimedean energy dominates the prime pairing: `A(F) − T_lam(F, F) ≥ 0`.

Proof.  The truncations `F χ_L` are not pole-free.  Subtract `c_L g₀`, `g₀` a fixed even bump
with `∫ g₀ e^{−u/2} > 0` and `c_L = ∫ F χ_L e^{−u/2} / ∫ g₀ e^{−u/2} → 0`.  The corrected test is
even and pole-free, so its Weil functional is nonnegative.  Polarization of the archimedean energy
(`farArch_sub_smul`) and of the prime pairing (`atomPairing_add_smul_expand`) write it as the
truncated energy of `F` plus `c_L` times a bracket that converges (it involves the truncations of
`F` and of `F + g₀`) plus `c_L²` times a constant.

**Consequences.**
* Pole-free strip positivity: `L(Φ Φ^#) ≥ 0` for even strip functions with `Φ(i/2) = 0`
  (`evenWeilDensity_specSq_nonneg_of_weilPositiveEvenPolar`).
* Positivity on nonnegative resonators with an even pole-free profile
  (`re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar`).
* The log-density ceiling `Σ_{n ≥ 2, m ≥ 1, nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)(log N)²` for large `N`
  (`even_log_density_le_of_polar`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral ResonatorProfile OddSector WeilPoleWeight

/-! ## Bookkeeping for real tests -/

theorem archPoleEnergy_eq_pole_add_farArch (X : ℝ → ℝ) :
    archPoleEnergy X = 2 * ((∫ u, X u * Real.exp (-u / 2)) * ∫ u, X u * Real.exp (u / 2)) +
      farArch X := by
  unfold archPoleEnergy farArch
  rw [paperFT_ofRealFun_I_div_two, paperFT_ofRealFun_neg_I_div_two, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem integral_mul_exp_half_eq_of_even {X : ℝ → ℝ} (hX : ∀ x, X (-x) = X x) :
    ∫ u, X u * Real.exp (u / 2) = ∫ u, X u * Real.exp (-u / 2) := by
  rw [← integral_neg_eq_self (fun u => X u * Real.exp (u / 2))]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show X (-u) * Real.exp (-u / 2) = X u * Real.exp (-u / 2)
  rw [hX]

theorem archPoleEnergy_eq_of_even {X : ℝ → ℝ} (hX : ∀ x, X (-x) = X x) :
    archPoleEnergy X = 2 * (∫ u, X u * Real.exp (-u / 2)) ^ 2 + farArch X := by
  rw [archPoleEnergy_eq_pole_add_farArch, integral_mul_exp_half_eq_of_even hX]
  ring

theorem truncTest_add_of_support {F g : ℝ → ℝ} (hgs : ∀ x, 1 < |x| → g x = 0) {L : ℝ}
    (hL : 2 ≤ L) : truncTest (fun x => F x + g x) L = fun u => truncTest F L u + g u := by
  funext u
  unfold truncTest
  by_cases hu : |u| ≤ L - 1
  · rw [bulkCutoff_eq_one hu]; ring
  · push Not at hu
    have hg0 : g u = 0 := hgs u (by linarith)
    simp only [hg0]; ring

theorem decayBound_add_of_support {F g : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hF : DecayBound F δ C)
    (hg : ContDiff ℝ 2 g) (hgs : ∀ x, 1 < |x| → g x = 0) :
    ∃ C' : ℝ, DecayBound (fun x => F x + g x) δ C' := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_abs_gt_eq_zero hgs
  obtain ⟨M₀, hM₀⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨M₁, hM₁⟩ := (hg.continuous_deriv (by norm_num)).bounded_above_of_compact_support
    hgc.deriv
  have hd0 : ∀ x, 1 < |x| → deriv g x = 0 := fun x hx => by
    have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
      exact hgs y hy
    rw [hev.deriv_eq]; simp
  set K := Real.exp (1 / 2 + δ) with hK
  have hC := hF.2.1
  have hKpos : 0 < K := Real.exp_pos _
  -- a function bounded by `M` and vanishing for `|x| > 1` decays like `M K e^{−(1/2+δ)|x|}`
  have hloc : ∀ (h : ℝ → ℝ) (M : ℝ), (∀ x, ‖h x‖ ≤ M) → (∀ x, 1 < |x| → h x = 0) → ∀ x,
      |h x| ≤ |M| * K * Real.exp (-((1 / 2 + δ) * |x|)) := by
    intro h M hM hz x
    by_cases hx : 1 < |x|
    · rw [hz x hx, abs_zero]; positivity
    · push Not at hx
      have h1 : 1 ≤ K * Real.exp (-((1 / 2 + δ) * |x|)) := by
        rw [hK, ← Real.exp_add]
        exact Real.one_le_exp (by nlinarith [abs_nonneg x])
      have h2 : |h x| ≤ |M| := (Real.norm_eq_abs (h x) ▸ hM x).trans (le_abs_self M)
      calc |h x| ≤ |M| := h2
        _ = |M| * 1 := by ring
        _ ≤ |M| * (K * Real.exp (-((1 / 2 + δ) * |x|))) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg M)
        _ = |M| * K * Real.exp (-((1 / 2 + δ) * |x|)) := by ring
  refine ⟨C + (|M₀| + |M₁|) * K, hF.1.add hg, by positivity, fun x => ?_⟩
  have hx0 := hloc g M₀ hM₀ hgs x
  have hx1 := hloc (deriv g) M₁ hM₁ hd0 x
  obtain ⟨hF0, hF1⟩ := hF.2.2 x
  have he : 0 < Real.exp (-((1 / 2 + δ) * |x|)) := Real.exp_pos _
  have hderiv : deriv (fun x => F x + g x) x = deriv F x + deriv g x :=
    deriv_add ((hF.1.differentiable (by norm_num)) x) ((hg.differentiable (by norm_num)) x)
  constructor
  · calc |F x + g x| ≤ |F x| + |g x| := abs_add_le _ _
      _ ≤ C * Real.exp (-((1 / 2 + δ) * |x|)) + |M₀| * K * Real.exp (-((1 / 2 + δ) * |x|)) :=
          add_le_add hF0 hx0
      _ ≤ (C + (|M₀| + |M₁|) * K) * Real.exp (-((1 / 2 + δ) * |x|)) := by
          have : 0 ≤ |M₁| * K * Real.exp (-((1 / 2 + δ) * |x|)) := by positivity
          linarith
  · rw [hderiv]
    calc |deriv F x + deriv g x| ≤ |deriv F x| + |deriv g x| := abs_add_le _ _
      _ ≤ C * Real.exp (-((1 / 2 + δ) * |x|)) + |M₁| * K * Real.exp (-((1 / 2 + δ) * |x|)) :=
          add_le_add hF1 hx1
      _ ≤ (C + (|M₀| + |M₁|) * K) * Real.exp (-((1 / 2 + δ) * |x|)) := by
          have : 0 ≤ |M₀| * K * Real.exp (-((1 / 2 + δ) * |x|)) := by positivity
          linarith

/-! ## Pole-free positivity on decaying even tests -/

/-- One corrected truncation: the identity `W(Fχ_L − c g₀) = E(L)`. -/
theorem farArch_sub_atomPairing_corrected {lam : ℕ → ℝ} {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (heven : ∀ x, F (-x) = F x) {L : ℝ} (hL : 2 ≤ L) (c : ℝ) :
    farArch (fun x => truncTest F L x - c * evenFarBump 0 x) -
        atomPairing lam (crossCorr (fun x => truncTest F L x - c * evenFarBump 0 x)
          (fun x => truncTest F L x - c * evenFarBump 0 x)) =
      (archPoleEnergy (truncTest F L) - 2 * (∫ u, truncTest F L u * Real.exp (-u / 2)) ^ 2 -
          atomPairing lam (crossCorr (truncTest F L) (truncTest F L))) +
        c * ((archPoleEnergy (truncTest F L) -
            2 * (∫ u, truncTest F L u * Real.exp (-u / 2)) ^ 2) -
          (archPoleEnergy (truncTest (fun x => F x + evenFarBump 0 x) L) -
            2 * (∫ u, truncTest (fun x => F x + evenFarBump 0 x) L u * Real.exp (-u / 2)) ^ 2) +
          farArch (evenFarBump 0) +
          (atomPairing lam (crossCorr (truncTest (fun x => F x + evenFarBump 0 x) L)
              (truncTest (fun x => F x + evenFarBump 0 x) L)) -
            atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) -
            atomPairing lam (crossCorr (evenFarBump 0) (evenFarBump 0)))) +
        c ^ 2 * (farArch (evenFarBump 0) -
          atomPairing lam (crossCorr (evenFarBump 0) (evenFarBump 0))) := by
  set T := truncTest F L with hTdef
  set g₀ := evenFarBump 0 with hg₀def
  have hg₀s : ∀ x, 1 < |x| → g₀ x = 0 := fun x hx => evenFarBump_eq_zero le_rfl (by linarith)
  have hTs : ∀ x, L < |x| → T x = 0 := fun x hx => truncTest_eq_zero hx.le
  have hg₀s' : ∀ x, L < |x| → g₀ x = 0 := fun x hx => hg₀s x (by linarith)
  have hTd : ContDiff ℝ 2 T := contDiff_truncTest hF L
  have hTc : HasCompactSupport T := hasCompactSupport_truncTest F L
  have hg₀d : ContDiff ℝ 2 g₀ := contDiff_evenFarBump 0
  have hg₀c : HasCompactSupport g₀ := hasCompactSupport_evenFarBump 0
  have hTe : ∀ x, T (-x) = T x := truncTest_neg heven L
  have hg₀e : ∀ x, g₀ (-x) = g₀ x := evenFarBump_neg 0
  have hsum : truncTest (fun x => F x + g₀ x) L = fun u => T u + g₀ u :=
    truncTest_add_of_support hg₀s hL
  have hsume : ∀ x, T (-x) + g₀ (-x) = T x + g₀ x := fun x => by rw [hTe, hg₀e]
  -- archimedean polarization
  have harch := farArch_sub_smul hTd hg₀d hTs hg₀s' c
  -- the pole parts
  have hfa1 := archPoleEnergy_eq_of_even hTe
  have hfa2 := archPoleEnergy_eq_of_even (X := fun u => T u + g₀ u) hsume
  -- the prime pairings
  have hap := atomPairing_add_smul_expand lam hTd.continuous hTc hg₀d.continuous hg₀c (-c)
  have hap1 := atomPairing_add_smul_expand lam hTd.continuous hTc hg₀d.continuous hg₀c 1
  simp only [one_mul, one_pow, mul_one] at hap1
  have e1 : (fun x => T x - c * g₀ x) = fun u => T u + -c * g₀ u := by funext u; ring
  rw [hsum, hfa1, hfa2, hap1, e1, hap]
  rw [show (fun x => T x + -c * g₀ x) = fun x => T x - c * g₀ x by funext u; ring, harch]
  ring

/-- **Pole-free positivity on decaying even tests.** -/
theorem archPoleEnergy_sub_atomPairing_nonneg_of_polar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) {δ C : ℝ} (hδ : 1 / 2 < δ) (hF : DecayBound F δ C)
    (hP : ∫ u, F u * Real.exp (-u / 2) = 0) :
    0 ≤ archPoleEnergy F - atomPairing lam (crossCorr F F) := by
  have hδ0 : 0 < δ := by linarith
  set g₀ := evenFarBump 0 with hg₀def
  have hg₀s : ∀ x, 1 < |x| → g₀ x = 0 := fun x hx => evenFarBump_eq_zero le_rfl (by linarith)
  have hg₀d : ContDiff ℝ 2 g₀ := contDiff_evenFarBump 0
  have hg₀c : HasCompactSupport g₀ := hasCompactSupport_evenFarBump 0
  set p₀ := ∫ u, g₀ u * Real.exp (-u / 2) with hp₀def
  have hp₀ : p₀ = 2 * farJ := by
    rw [hp₀def, hg₀def, integral_evenFarBump_mul_exp]; norm_num
  have hp₀pos : 0 < p₀ := by rw [hp₀]; linarith [farJ_pos]
  -- limits of the truncated quantities
  have hE : ExpDecayTest F := hF.expDecayTest hδ0
  obtain ⟨C', hFg⟩ := decayBound_add_of_support hδ0 hF hg₀d hg₀s
  have hEg : ExpDecayTest (fun x => F x + g₀ x) := hFg.expDecayTest hδ0
  have hb : 1 < 1 / 2 + δ := by linarith
  have hA := tendsto_archPoleEnergy_truncTest hE
  have hAg := tendsto_archPoleEnergy_truncTest hEg
  have hT := tendsto_atomPairing_truncTest_of_growth hg hE hb hF.2.1 fun x => (hF.2.2 x).1
  have hTg := tendsto_atomPairing_truncTest_of_growth hg hEg hb hFg.2.1 fun x => (hFg.2.2 x).1
  have hhalf : |(-(1 / 2) : ℝ)| ≤ 1 / 2 := by norm_num [abs_of_pos]
  have ehalf : ∀ u : ℝ, -(1 / 2) * u = -u / 2 := fun u => by ring
  have hP0 := tendsto_integral_truncTest_mul_exp hδ0 hF hhalf
  have hPg0 := tendsto_integral_truncTest_mul_exp hδ0 hFg hhalf
  simp_rw [ehalf] at hP0 hPg0
  rw [hP] at hP0
  have hc := hP0.div_const p₀
  rw [zero_div] at hc
  -- the expression `E(L)` and its limit
  have hlim := ((hA.sub ((hP0.pow 2).const_mul 2)).sub hT).add
    ((hc.mul ((((hA.sub ((hP0.pow 2).const_mul 2)).sub (hAg.sub ((hPg0.pow 2).const_mul 2))).add
      (tendsto_const_nhds (x := farArch g₀))).add ((hTg.sub hT).sub
        (tendsto_const_nhds (x := atomPairing lam (crossCorr g₀ g₀)))))).add
      ((hc.pow 2).mul (tendsto_const_nhds (x := farArch g₀ -
        atomPairing lam (crossCorr g₀ g₀)))))
  refine (ge_of_tendsto hlim ?_).trans_eq (by ring)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  set c := (∫ u, truncTest F L u * Real.exp (-u / 2)) / p₀ with hcdef
  set G : ℝ → ℝ := fun x => truncTest F L x - c * g₀ x with hGdef
  have hGd : ContDiff ℝ 2 G := (contDiff_truncTest hF.1 L).sub (contDiff_const.mul hg₀d)
  have hGs : ∀ x, L < |x| → G x = 0 := fun x hx => by
    simp only [hGdef, truncTest_eq_zero hx.le, hg₀s x (by linarith), mul_zero, sub_zero]
  have hGc := hasCompactSupport_of_abs_gt_eq_zero hGs
  have hGe : ∀ x, G (-x) = G x := fun x => by
    simp only [hGdef, truncTest_neg heven L x, hg₀def, evenFarBump_neg]
  have hiT : Integrable fun u => truncTest F L u * Real.exp (-u / 2) :=
    ((contDiff_truncTest hF.1 L).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_truncTest F L).mul_right
  have hig : Integrable fun u => g₀ u * Real.exp (-u / 2) :=
    (hg₀d.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hg₀c.mul_right
  have hGP : ∫ u, G u * Real.exp (-u / 2) = 0 := by
    have e : (fun u => G u * Real.exp (-u / 2)) =
        fun u => truncTest F L u * Real.exp (-u / 2) - c * (g₀ u * Real.exp (-u / 2)) := by
      funext u; simp only [hGdef]; ring
    rw [e, integral_sub hiT (hig.const_mul c), integral_const_mul, ← hp₀def, hcdef,
      div_mul_cancel₀ _ hp₀pos.ne', sub_self]
  have hpos := hpf (fun u => (G u : ℂ)) (contDiff_ofReal_comp hGd)
    (hGc.comp_left Complex.ofReal_zero) (fun x => by simp only [hGe])
    (by rw [paperFT_ofRealFun_I_div_two, hGP, Complex.ofReal_zero])
  rw [re_weilFullFunctional_ofReal_eq lam hGd.continuous hGc,
    re_weilPoleTerm_ofReal_even hGd.continuous hGc hGe, hGP] at hpos
  have key := farArch_sub_atomPairing_corrected (lam := lam) hF.1 heven hL c
  rw [← hGdef] at key
  linarith

/-! ## Strip functions, resonators and the ceiling -/

/-- **Pole-free strip positivity without a pole weight.** -/
theorem evenWeilDensity_specSq_nonneg_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) (hΦ0 : Φ (I / 2) = 0) : 0 ≤ evenWeilDensity lam (specSq Φ) := by
  obtain ⟨ε, C, hε, hs⟩ := hΦ.strip
  rw [evenWeilDensity_specSq (by norm_num : (1 : ℝ) / 2 < 5 / 4) hε hs hΦ.sym]
  have hD := decayBound_stripTest (by norm_num : (1 : ℝ) / 2 < 5 / 4) hε hs
  have hval : ((∫ u, stripTest Φ u * Real.exp (-u / 2) : ℝ) : ℂ) = Φ (I / 2) := by
    rw [← paperFT_ofRealFun_I_div_two]
    exact paperFT_stripTest (by norm_num) hε hs hΦ.sym (by simp; norm_num)
  refine archPoleEnergy_sub_atomPairing_nonneg_of_polar hpf hg (stripTest_neg hΦ.even)
    (by norm_num) hD ?_
  exact_mod_cast hval.trans hΦ0

/-- **Positivity on nonnegative resonators with an even pole-free profile.** -/
theorem re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {Cg : ℝ}
    (hgr : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    {ι : Type*} (s : Finset ι) {c : ι → ℝ} (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ) {g : ℝ → ℝ}
    (hg2 : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hge : ∀ u, g (-u) = g u)
    (hg0 : paperFT (fun u => (g u : ℂ)) (I / 2) = 0) :
    0 ≤ (weilFullFunctional lam
      (EF.weilTest (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ))
        (fun u => ((∑ k ∈ s, c k * g (u - x k) : ℝ) : ℂ)))).re :=
  re_weilFullFunctional_translateSum_nonneg hgr
    (fun _ hA hA0 => evenWeilDensity_specSq_nonneg_of_weilPositiveEvenPolar hpf hgr hA hA0) s hc x
    hg2 hgc hge hg0

theorem integral_weilAtomSymbol_unitResonator_nonneg_of_polar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {Cg : ℝ}
    (hgr : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) (N : ℕ) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (resonator N (unitResonatorCoeff N) (1 / ((N : ℝ) + 1))) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊
        (τ / (2 * π)) := by
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨hp1, hp2⟩ := paperFT_resonator_pole (N := N) (c := unitResonatorCoeff N) hw
  have ha : 0 ≤ Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4 := by
    have := Real.log_natCast_nonneg N
    positivity
  refine integral_weilAtomSymbol_nonneg_of_polar ha (contDiff_resonator N _ _ 2)
    (tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (fun v hv => gC_eq_zero hw hv) hu) hp1 hp2 ?_
  have hgc : HasCompactSupport (gR (1 / ((N : ℝ) + 1))) :=
    (hasCompactSupport_comp_left (g := Complex.ofReal) fun {_} => Complex.ofReal_eq_zero).mp
      (hasCompactSupport_gC hw)
  rw [resonator_unitResonatorCoeff]
  exact re_weilFullFunctional_translateSum_nonneg_of_weilPositiveEvenPolar hpf hgr
    (Finset.Icc 1 N) (c := fun m => 1 / Real.sqrt m) (fun m _ => by positivity) (resPt N)
    (contDiff_gR _ 2) hgc (gR_neg _) (paperFT_gC_pole hw).1

/-- **The unit Weil–Toeplitz bound for even pole-free positive weights.** -/
theorem even_unit_toeplitz_bound_of_polar {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam)
    {Cg : ℝ} (hgr : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {N : ℕ}
    (hN : 1 ≤ N) :
    2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then lam n / (n * m) else 0) ≤
      (Real.log N + (Real.log 2 + 9 / 2 + profileRatio / 2)) *
        ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
  have hc : ∀ m, N < m → unitResonatorCoeff N m = 0 := fun m hm => by
    simp [unitResonatorCoeff, not_le.mpr hm]
  have hb := weil_multiplicativeToeplitz_bound_of_resonator hN (unitResonatorCoeff N) hc
    (integral_weilAtomSymbol_unitResonator_nonneg_of_polar hpf hgr N)
  have hlhs : ∀ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, unitResonatorCoeff N (n * m) * conj (unitResonatorCoeff N m)).re =
      ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then lam n / (n * m) else 0) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    by_cases hnm : n * m ≤ N
    · rw [if_pos hnm]
      simp only [unitResonatorCoeff, if_pos hnm, if_pos hmN, Complex.conj_ofReal,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      have hsq : Real.sqrt ((n * m : ℕ) : ℝ) = Real.sqrt n * Real.sqrt m := by
        push_cast; exact Real.sqrt_mul hn1.le _
      rw [hsq]
      have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn1.le
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn1
      have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
      calc lam n / Real.sqrt n * (1 / (Real.sqrt n * Real.sqrt m) * (1 / Real.sqrt m))
          = lam n / ((Real.sqrt n * Real.sqrt n) * (Real.sqrt m * Real.sqrt m)) := by
            field_simp
        _ = lam n / (n * m) := by rw [hsn, hsm]
    · rw [if_neg hnm]
      simp [unitResonatorCoeff, if_neg hnm]
  have hrhs : ∑ m ∈ Finset.Icc 1 N, ‖unitResonatorCoeff N m‖ ^ 2 =
      ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    simp only [unitResonatorCoeff, if_pos hmN, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_pow, one_pow, Real.sq_sqrt hm0.le]
  rw [Finset.sum_congr rfl hlhs, hrhs] at hb
  exact hb

/-- **The log-density ceiling of even pole-free positive weights.** -/
theorem even_log_density_le_of_polar {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam)
    {Cg : ℝ} (hgr : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then lam n / (n * m) else 0) ≤ (1 / 2 + ε) * Real.log N ^ 2 := by
  set C₀ : ℝ := Real.log 2 + 9 / 2 + profileRatio / 2 with hC₀
  set L₀ : ℝ := 2 * (|C₀| + 1) / ε + |C₀| + 1 with hL₀
  refine ⟨⌈Real.exp L₀⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : L₀ ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNr]
    have h1 : Real.exp L₀ ≤ ⌈Real.exp L₀⌉₊ := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈Real.exp L₀⌉₊ ≤ N by omega)
    linarith
  have hq0 : 0 ≤ 2 * (|C₀| + 1) / ε := by positivity
  have hL1 : 1 ≤ L₀ := by rw [hL₀]; linarith [abs_nonneg C₀]
  set L := Real.log N with hLdef
  have hχ := even_unit_toeplitz_bound_of_polar hpf hgr hN1
  have hH := sum_Icc_inv_le_one_add_log N
  have hLC : 0 ≤ L + C₀ := by
    have h1 : |C₀| + 1 ≤ L₀ := by rw [hL₀]; linarith
    linarith [neg_abs_le C₀]
  have hstep : 2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then lam n / (n * m) else 0) ≤ (L + C₀) * (1 + L) :=
    hχ.trans (mul_le_mul_of_nonneg_left hH hLC)
  have hquad : (L + C₀) * (1 + L) ≤ (1 + 2 * ε) * L ^ 2 := by
    have hLpos : 1 ≤ L := hL1.trans hlog
    have hdiv : 2 * (|C₀| + 1) / ε ≤ L := by rw [hL₀] at hlog; linarith [abs_nonneg C₀]
    have hbig : 2 * (|C₀| + 1) ≤ L * ε := (div_le_iff₀ hε).mp hdiv
    have hC : C₀ ≤ |C₀| := le_abs_self C₀
    have h1 : (L + C₀) * (1 + L) ≤ L ^ 2 + 2 * (|C₀| + 1) * L := by nlinarith [abs_nonneg C₀]
    have h2 : 2 * (|C₀| + 1) * L ≤ ε * L ^ 2 := by nlinarith
    nlinarith
  linarith

end RHTower.EvenSector

end
