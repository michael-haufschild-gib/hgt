import Zeta23.Final
import GaloisForLFunctions.RHTower.RankTraceSpectralSlack

/-!
# Alpöge–Furman's two-thirds theorem with its spectral slack retained

The two-thirds theorem bounds `N₀*(T, 2T)` below through the zero-side decomposition
`Â = P + Q` of the hat-unit Gram matrix: `P ⪰ 0` collects the critical-line zeros and `Q` the
off-line pairs `{ρ, 1 − ρ̄}`.  Its rank–trace step discards the nonnegative quantity

`S(T) := 2 · tr Q₋ + ∑_{q ∈ spec Q, q > 0} (q − 2)² + ∑_{p ≠ 0} (p − 1 − m)²`

(`RHTower.rank_trace_ineq_slack` at `c = 2`), where `p` and `m` run over the eigenvalues of `P` and
of `Q₋` in decreasing order.

**Theorem** (`thmA_lam_spectralSlack`).  For every `λ ∈ (0, 1)` and `ε > 0`, for all large `T`,

`(H(λ) − ε) · N(T, 2T) + S_λ(T) ≤ N₀*(T, 2T)`,

where `S_λ(T)` (`zeroSideSlack`) is built from the zeros of `ζ` with ordinate in
`(T − √T, 2T + √T]` and the test vectors of bandwidth `λ`, and `H(λ) = 2 − 1/λ − λ/3`.

Both parts of the slack are rigid.  An isolated off-line pair at displacement
`a = (β − ½) log T` contributes a block with eigenvalues `m(g + 1)` and `−m(g − 1)`, where `g ≥ 1`
grows with `a`.  When `Q₋ = 0`, the on-line part is `∑_{μ ∈ spec P, μ ≠ 0} (μ − 1)²`, which vanishes
only when `P` is an orthogonal projection, i.e. when the on-line test vectors are orthonormal.  So
an on-line count near the two-thirds bound forces a nearly orthonormal on-line frame, which for
`sinc`-type kernels means ordinates nearly on a lattice of spacing `2π/L`.

The proof is Alpöge–Furman's assembly (`Zeta23.Assembly.thmA_abstract_err`, adapted from the
vendored `Zeta23` package, Apache-2.0) with the zero-side core replaced by
`RHTower.zeroside_rank_core_slack`.
-/

noncomputable section

open Filter Topology Asymptotics Matrix
open RHLinalg
open scoped ComplexOrder

namespace RHTower

open Zeta23 Zeta23.Assembly

/-- The off-line spectral slack at height `T`: `2 tr Q₋ + ∑_{q > 0} (q − 2)²` for the hat-unit
off-line block `Q` of the zero configuration `Z` at bandwidth parameters `P`. -/
def offLineSpectralSlack (Z : ZeroConfig) (P : Params) (T : ℝ) : ℝ :=
  2 * rtrace (hermNegPart
      (ZeroSide.hatQ_isHermitian Z T P (fun z => GzGp.phiHat_conj P T z)))
    + posSlack (ZeroSide.hatQ_isHermitian Z T P (fun z => GzGp.phiHat_conj P T z)) 2

lemma offLineSpectralSlack_nonneg (Z : ZeroConfig) (P : Params) (T : ℝ) :
    0 ≤ offLineSpectralSlack Z P T := by
  unfold offLineSpectralSlack
  have h1 : 0 ≤ rtrace (hermNegPart
      (ZeroSide.hatQ_isHermitian Z T P (fun z => GzGp.phiHat_conj P T z))) := by
    rw [rtrace_hermNegPart]
    exact Finset.sum_nonneg fun i _ => negPart_nonneg _
  have h2 := posSlack_nonneg
      (ZeroSide.hatQ_isHermitian Z T P (fun z => GzGp.phiHat_conj P T z)) 2
  linarith

/-- The on-line Parseval defect at height `T`: the slack `∑_{p ≠ 0} (p − 1 − m)²` of the rank–trace
step for the hat-unit on-line block `P ⪰ 0` (eigenvalues `p`) against the negative part of the
off-line block (eigenvalues `m`), both in decreasing order.  It is `0` outside the regime
`a L² > 0` where `P ⪰ 0` is available. -/
def onLineParsevalDefect (Z : ZeroConfig) (P : Params) (T : ℝ) : ℝ :=
  if hc : 0 < P.a T * P.L T ^ 2 then
    onSlack (ZeroSide.hatP_posSemidef Z T P (fun z => GzGp.phiHat_conj P T z) hc).isHermitian
      (ZeroSide.hatQ_isHermitian Z T P (fun z => GzGp.phiHat_conj P T z)) 2
  else 0

lemma onLineParsevalDefect_nonneg (Z : ZeroConfig) (P : Params) (T : ℝ) :
    0 ≤ onLineParsevalDefect Z P T := by
  unfold onLineParsevalDefect
  split_ifs
  · exact onSlack_nonneg _ _ 2
  · exact le_rfl

/-- The total zero-side slack: off-line spectral slack plus on-line Parseval defect. -/
def zeroSideSlack (Z : ZeroConfig) (P : Params) (T : ℝ) : ℝ :=
  offLineSpectralSlack Z P T + onLineParsevalDefect Z P T

lemma zeroSideSlack_nonneg (Z : ZeroConfig) (P : Params) (T : ℝ) : 0 ≤ zeroSideSlack Z P T :=
  add_nonneg (offLineSpectralSlack_nonneg Z P T) (onLineParsevalDefect_nonneg Z P T)

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- **Seam A with slack.**  For `T ≥ 0`, with `Ĝ := P.hat T (Z.Gz P T)` and `B₀ := θ₀/(aL)`:
`4 tr Ĝ − ‖Ĝ‖_F² − 2N(T,2T) − 3N(I′∖I) − B₀(4 + 2‖Ĝ‖_F + B₀) + S(T) ≤ N₀*(T,2T)`, with `S` the
total zero-side slack (`zeroSideSlack`). -/
theorem seamA_spectralSlack (hT : 0 ≤ T) (hPois : ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T) * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T)))
          + θ₀ / (P.a T * P.L T))
      + zeroSideSlack Z P T
      ≤ Z.N0star T (2 * T) := by
  have hconj : ZeroSide.PhiHatConj T P := fun z => GzGp.phiHat_conj P T z
  have hreal : ZeroSide.PhiHatReal T P := fun r => GzGp.phiHat_ofReal P T r
  have hc : 0 < P.a T * P.L T ^ 2 := mul_pos ha (pow_pos hL 2)
  have hdec := ZeroSide.hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hPm := ZeroSide.hatP_posSemidef Z T P hconj hc
  have hQm := ZeroSide.hatQ_isHermitian Z T P hconj
  have hrank := ZeroSide.rank_hatP_le Z T P hconj hc
  have htrP := ZeroSide.rtrace_hatP_le Z T P hconj hreal hPois hc
  have hpos := ZeroSide.posIndex_hatQ_le Z T P hconj hc hQm
  have hcount : (Z.NonIprime T : ℝ) + 2 * (Z.p T : ℝ) ≤ (Z.NIprime T : ℝ) := by
    exact_mod_cast ZeroSide.NonIprime_add_two_p_le_NIprime Z T
  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := zeroside_rank_core_slack hdec hPm hQm hrank hpos htrP hcount
  have hpert := four_tr_sub_frobSq_perturb hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hcount' : ((Z.s1 T + Z.s2 T : ℕ) : ℝ) ≤ (Z.N0star T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_add_s2_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  have hS : zeroSideSlack Z P T
      = 2 * rtrace (hermNegPart hQm) + posSlack hQm 2 + onSlack hPm.isHermitian hQm 2 := by
    rw [zeroSideSlack, onLineParsevalDefect, dif_pos hc]; rfl
  rw [hNI] at hcore
  rw [hS]
  push_cast at hcount' hcore
  linarith

section MainSlack
open Filter Asymptotics Topology

/-- **Theorem A at fixed `λ ∈ (0,1)` with the off-line spectral slack**, abstract zero
configuration: Alpöge–Furman's `thmA_abstract_err`, with `seamA` replaced by
`seamA_spectralSlack`. -/
theorem thmA_abstract_err_spectralSlack (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (Err : ℝ → ℝ)
    (hTr : TracesBoundsE P Err P.a P.trGtilde P.trGtildeSq (fun T => (Z.N T (2 * T) : ℝ)))
    (hPois : ∀ᶠ T in atTop, ZeroSide.PoissonSq T P)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)
    (hcalE : Tendsto Err atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) + zeroSideSlack Z P T ≤ Z.N0star T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTr.tr2
  obtain ⟨CN, T₃, hRvMmain⟩ := hRvM.main
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  -- the functions of T (abbreviations)
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => 1 / P.lam1 T + P.lam1 T / 3 with hcl
  set K : ℝ → ℝ := fun T => (1 + C₂ * Err T) / P.a T ^ 2 with hK
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / P.a T with hR₁
  set R₂ : ℝ → ℝ := fun T => cl T * ((K T - 1) * N T + K T * (|CN| * Real.log T)) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) + 1 / (P.lam * l T) * N T with herr
  -- basic limits
  have hLtop := tendsto_L_atTop P hlam0
  have ha1 := tendsto_a_one P hlam0 ha
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hcE0 : Tendsto (fun T => C₂ * Err T) atTop (𝓝 0) := by
    simpa using hcalE.const_mul C₂
  have hKto : Tendsto K atTop (𝓝 1) := by
    have h1 : Tendsto (fun T => 1 + C₂ * Err T) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hcE0
    have h2 : Tendsto (fun T => P.a T ^ 2) atTop (𝓝 1) := by simpa using ha1.pow 2
    simpa [hK, Pi.div_def] using h1.div h2 one_ne_zero
  ------------------------------------------------------------------
  -- (1) the main inequality, eventually in T
  ------------------------------------------------------------------
  have hmain : ∀ᶠ T in atTop,
      Hfun P.lam * N T - err T ≤ (Z.N0star T (2 * T) : ℝ) - zeroSideSlack Z P T := by
    filter_upwards [hPois, hTail, hGzGp, hapos, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop T₃, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_log_nonneg, hcE0.eventually (eventually_gt_nhds (show (-1:ℝ) < 0 by norm_num))]
      with T hPT hTl hGG ha2 hT₁ hT₂ hT₃ hT0 hl hlog hcE
    have hapos' : 0 < P.a T := by linarith
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hℓ₁ := ell1_pos hl
    have hKnn : 0 ≤ 1 + C₂ * Err T := by linarith
    -- Seam A
    have hA := seamA_spectralSlack hT0 hPT hTl hapos' hLpos
    -- Seam B
    have htr2' : P.trGtildeSq T - P.mainTr2 T ≤ C₂ * Err T * P.mainTr2 T := by
      have := htr2 T hT₂
      simp only at this
      rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM' : T * ell1 T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvMmain T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := seamB hGG hapos' hLpos hℓ₁ htr1' hKnn htr2' hRvM'
    -- combine with N0star_lower_H and H(λ₁) ≥ H(λ) − 1/(λ l)
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have hA' : 4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
        - θ₀ T / (P.a T * P.L T) * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T)))
          + θ₀ T / (P.a T * P.L T))
        ≤ (Z.N0star T (2 * T) : ℝ) - zeroSideSlack Z P T := by linarith
    have h := N0star_lower_H hB₀ hA' hSB.1 hSB.2
    have hH := Hfun_lam1_ge P T hlam0 hl
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hHN : (Hfun P.lam - 1 / (P.lam * l T)) * N T ≤ Hfun (P.lam1 T) * N T :=
      mul_le_mul_of_nonneg_right hH hN0
    simp only [herr, hR₁, hR₂, hBdef, hcl, hK, hNdef] at h hHN ⊢
    linarith
  ------------------------------------------------------------------
  -- (2) err = o(N)
  ------------------------------------------------------------------
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z hRvM
  -- R₁ = o(N)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- R₂ = o(N)
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 / P.lam + 1 / 3) ?_
      filter_upwards [eventually_clam_bounds P hlam0 hlam1] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0:ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1:ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      isLittleO_of_bdd_mul hKO ((isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_log_Tl).const_mul_left _)
    exact isLittleO_of_bdd_mul hclO (i1.add i2)
  -- N(I′∖I) = o(N)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_sqrt_mul_l_Tl)
  -- B → 0
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, hapos, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by positivity)
    · filter_upwards [hTail, hapos, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < P.a T := by linarith
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr
  -- the bracket and the 1/(λ l) term
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B) (cl := cl)
    hNtop o1 o2 o3 o4 (eventually_clam_bounds P hlam0 hlam1)
  have o6 : (fun T => 1 / (P.lam * l T) * N T) =o[atTop] N :=
    isLittleO_of_tendsto_zero_mul (tendsto_const_nhds.div_atTop (tendsto_l_atTop.const_mul_atTop hlam0))
  have herr_o : err =o[atTop] N := o5.add o6
  ------------------------------------------------------------------
  -- (3) conclude
  ------------------------------------------------------------------
  have hfin := eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hfin ε hε
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; simp only [hNdef] at this; linarith⟩


/-- Lemma `lem:poisson` eventually in `T`, as consumed by `seamA_spectralSlack`. -/
lemma eventually_poissonSq (P : Params) (hP : P.Valid) :
    ∀ᶠ T in atTop, ZeroSide.PoissonSq T P := by
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T :=
    (Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop _
  filter_upwards [hwL] with T hwL
  exact fun γ => Params.hasSum_phiHatR_sq hP hwL γ

/-- **Theorem A with spectral slack, for `ζ`, unconditional.**  For every
`λ ∈ (0, 1)` and `ε > 0`, for all large `T`,
`(H(λ) − ε) · N(T, 2T) + S_λ(T) ≤ N₀*(T, 2T)`, where `S_λ(T) ≥ 0` is the zero-side slack: the
off-line part `2 tr Q₋ + ∑_{q > 0} (q − 2)²` plus the on-line Parseval defect
`∑_{p ≠ 0} (p − 1 − m)²` of the hat-unit blocks of the zeros of `ζ` at bandwidth `λ`. -/
theorem thmA_lam_spectralSlack {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (Ncount T (2 * T) : ℝ)
        + zeroSideSlack zetaZeroConfig (paramsOf stdProfile lam) T
        ≤ N0star T (2 * T) := by
  have H := paperInputs_zeta
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have hTr := PrimeSide.thm_traces hP H
  obtain ⟨hGzGp, ha, hNII, hcalE⟩ := eventually_side_conditions zetaZeroConfig H _ hP
  obtain ⟨θ₀, hTail, hθ₀⟩ := Tail.eventually_tailPackage zetaZeroConfig H _ hP
  have h := thmA_abstract_err_spectralSlack zetaZeroConfig H.RvM (paramsOf stdProfile lam) hP h1
    (paramsOf stdProfile lam).calE hTr.toE (eventually_poissonSq _ hP) θ₀ hTail hθ₀ hNII hGzGp ha
    hcalE
  have hlam : (paramsOf stdProfile lam).lam = lam := rfl
  rw [hlam] at h
  simpa using h

end MainSlack

end RHTower
