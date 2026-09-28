import GaloisForLFunctions.RHTower.QuasiPolynomialWeilSeparation

/-!
# The Landau-sharp inertia law

`WeilNyquistInertia` shows that `3/2`-separated off-line zeros of `ζ` below `≈ 2e^{2a-3/4}`
give independent negative squares of the level-`a` Weil form. This file raises the horizon to
the Landau value and the margin to quasi-polynomial size, using the tilted cluster tests of
`TiltedClusterNyquistExclusion`.

**Theorem** (`weilNegIndex_ge_card_tilted`). For every tilt `0 ≤ θ < π/4`, let `T` be a finite
set of zeros with `β > ½`, `t ≥ 101`, pairwise ordinate gaps `≥ 3/2`, with `tiltedHodgeRatio ≤ R`,
`tiltedNormRatio ≤ Λ` and `K₀ |T| R ≤ 1`. Then `|T| ≤ weilNegIndex ζ a (1/(K₁ a |T| (Λ² + 1)))`.

Each zero is represented by its tilted cluster test, normalized by `e^{-θ(t - 3/4)}`, so that
its node values have modulus between `1` and `e^{3θ/2}`. Three ingredients follow.

* **Diagonal** (`ClusterSetup.re_W_testθ_le`): `-3/8 + (5/4) S_Z (B/A)²`.
* **Cross terms** (`norm_W_tilted_tests_le`): a zero is a node of at most one test, and the other
  test sees only its decaying tail there. Otherwise both tails decay, so
  `‖W(f, f')‖ ≤ (5/4) S_Z (V B' + V' B + B B')`.
* **Gram step**: the diagonally dominant Gram matrix gives a `|T|`-dimensional negative subspace
  (`exists_negative_subspace_of_gram`).
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "shw" => OffLinePairData.sh
local notation "Mt" => tiltedPhiTailConst

/-! ## Scalars and pointwise bounds for the Weil form -/

theorem paperFT_const_mul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    paperFT (fun u => c * f u) z = c * paperFT f z := by
  unfold paperFT
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem W_const_mul (c d : ℂ) (f g : ℝ → ℂ) :
    zetaZeroConfig.W (fun u => c * f u) (fun u => d * g u) =
      c * (starRingEnd ℂ) d * zetaZeroConfig.W f g := by
  unfold ZeroConfig.W
  rw [← tsum_mul_left]
  congr 1; funext ρ
  unfold ZeroConfig.Wsummand
  rw [paperFT_const_mul, paperFT_const_mul, map_mul]
  ring

/-- **Pointwise bound for the Weil form.** If `‖f̂(γ_ρ)‖ ‖ĝ(conj γ_ρ)‖ ≤ C/(1 + |t_ρ|)²` at every
zero, then `‖W(f,g)‖ ≤ (5/4) S_Z C`. -/
theorem norm_W_le_of_pointwise {f g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖paperFT f (gammaOf (ρ : ℂ))‖ * ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤
        C / (1 + |(ρ : ℂ).im|) ^ 2) :
    ‖zetaZeroConfig.W f g‖ ≤ (5 / 4) * zeroSumZ * C := by
  have hb : ∀ ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f g ρ‖ ≤
      (5 / 4) * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    intro ρ
    have hn : ‖zetaZeroConfig.Wsummand f g ρ‖ = (zetaZeroConfig.mult ρ : ℝ) *
        (‖paperFT f (gammaOf (ρ : ℂ))‖ * ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖) := by
      simp only [ZeroConfig.Wsummand]
      rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]; ring
    rw [hn]
    have hq := one_div_one_add_abs_im_sq_le (zetaZeroConfig.strip _ ρ.2)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have h1 : C / (1 + |(ρ : ℂ).im|) ^ 2 ≤ (5 / 4) * C *
        (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
      rw [div_eq_mul_one_div]
      calc C * (1 / (1 + |(ρ : ℂ).im|) ^ 2)
          ≤ C * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
            mul_le_mul_of_nonneg_left hq hC
        _ = _ := by ring
    calc (zetaZeroConfig.mult ρ : ℝ) *
          (‖paperFT f (gammaOf (ρ : ℂ))‖ * ‖paperFT g ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * ((5 / 4) * C *
            (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul_of_nonneg_left ((hpt ρ).trans h1) hm
      _ = _ := by ring
  have hsB : Summable (fun ρ : zetaZeroConfig.carrier =>
      (5 / 4) * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
    summable_zeroSumZ.mul_left _
  have hs : Summable (fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f g ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsB
  calc ‖zetaZeroConfig.W f g‖ = ‖∑' ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand f g ρ‖ := by
        rw [ZeroConfig.W]
    _ ≤ ∑' ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f g ρ‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' ρ : zetaZeroConfig.carrier,
          (5 / 4) * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
        Summable.tsum_le_tsum hb hs hsB
    _ = (5 / 4) * C * zeroSumZ := by rw [tsum_mul_left]; rfl
    _ = (5 / 4) * zeroSumZ * C := by ring

namespace ClusterSetup

variable (C : ClusterSetup)

/-- The truncation defect `η = 6 Σ|c_k| tail(K_θ)` of the tilted test. -/
def tiltDefect (θ a : ℝ) : ℝ := 6 * coeffMass C.Q * expTail (C.Kθ θ) (1 / 2) (a - 1 / 4 - shw)

theorem tiltDefect_nonneg (θ a : ℝ) : 0 ≤ C.tiltDefect θ a := by
  unfold tiltDefect
  exact mul_nonneg (mul_nonneg (by norm_num) (coeffMass_nonneg _)) (expTail_nonneg _ _ _)

theorem tiltDefect_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : XiDivisorSupport}
    (hρ₀ : ρ₀ ∈ C.nodes) (a : ℝ) {Kp : ℝ} (hKp0 : 0 ≤ Kp) :
    C.tiltDefect θ a ≤ (6 * coeffMass C.Q * C.tailDecay θ a Kp) / 2 := by
  obtain ⟨k₁, k₂, -, -, -, -, t0, -, -⟩ := C.Kθ_calculus hθ0 hθ hρ₀
  have e0 := t0 (1 / 2) (a - 1 / 4 - shw) (by norm_num)
  set τ := 2 ^ windowCount C.t₀ *
    expTail (tiltedPhi θ) (1 / 2 + 3 / 2 * windowCount C.t₀) (a - 1 / 4 - shw) with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; exact mul_nonneg (by positivity) (expTail_nonneg _ _ _)
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  have hdec : 2 * τ ≤ C.tailDecay θ a Kp := by
    unfold tailDecay
    rw [← hτ]
    have : 1 ≤ (1 + Kp) + 2 * Kp * (1 + (C.t₀ + 2)) + (1 + (C.t₀ + 2)) ^ 2 := by
      have : 0 ≤ 2 * Kp * (1 + (C.t₀ + 2)) := by positivity
      have : 0 ≤ (1 + (C.t₀ + 2)) ^ 2 := sq_nonneg _
      linarith
    nlinarith
  unfold tiltDefect
  have hc := coeffMass_nonneg C.Q
  have := mul_le_mul_of_nonneg_left e0 (by positivity : (0 : ℝ) ≤ 6 * coeffMass C.Q)
  nlinarith

/-- The tilted test at a node is at most `e^{θ(t₀ + 3/4)} + η`. -/
theorem norm_testθ_node_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (a : ℝ)
    {ν : XiDivisorSupport} (hν : ν ∈ C.nodes) :
    ‖paperFT (C.testθ θ a) (gammaOf (ν : ℂ))‖ ≤
      Real.exp (θ * (C.t₀ + 3 / 4)) + C.tiltDefect θ a := by
  obtain ⟨Y, hY, hYn⟩ := C.testθ_at_node hθ0 hθ a hν
  rw [hY]
  refine (norm_sub_le _ _).trans (add_le_add ?_ hYn)
  rw [norm_mul, norm_sgn, mul_one, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (gammaOf (ν : ℂ) * θ).re = (ν : ℂ).im * θ := by
    rw [Complex.mul_re, WeilEF.gammaOf_re]; simp
  rw [hre]
  have hc := (C.node_coords hν).1
  have hX := C.hX2
  have h1 : (ν : ℂ).im ≤ C.t₀ + 3 / 4 := by
    have := abs_lt.mp (lt_of_lt_of_le hc hX)
    rw [WeilEF.gammaOf_re] at this
    linarith [this.2]
  nlinarith

/-- At a zero of `Ξ` that is not a node, the tilted test decays with constant `B_d`. -/
theorem testθ_off_support {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : XiDivisorSupport}
    (hρ₀ : ρ₀ ∈ C.nodes) (a : ℝ) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp)
    {μ : XiDivisorSupport} (hμ : μ ∉ C.nodes) :
    (1 + |(μ : ℂ).im|) ^ 2 * ‖paperFT (C.testθ θ a) (gammaOf (μ : ℂ))‖ ≤
      6 * coeffMass C.Q * C.tailDecay θ a Kp := by
  obtain ⟨-, hprod, -⟩ := C.K_spec
  have hdiv : divisorEval C.L (gammaOf (μ : ℂ)) ≠ 0 := by
    refine C.divisorEval_ne_zero_of_not_node fun ν hν e => hμ ?_
    have : μ = ν := Subtype.ext (gammaOf_injective e)
    rw [this]; exact hν
  have hK0 : paperFT C.K (gammaOf (μ : ℂ)) = 0 := by
    have h := hprod (gammaOf (μ : ℂ))
    rw [riemannXiHat_gammaOf_eq_zero (divisorSupport_mem_carrier μ)] at h
    exact (mul_eq_zero.mp h).resolve_left hdiv
  have h := C.testθ_off hθ0 hθ hρ₀ a hKp2 hKp (abs_gammaOf_divisorSupport_im_lt μ).le hK0
  rwa [WeilEF.gammaOf_re] at h

/-- **The tilted test without positivity.** If `η ≤ A/8`, `A = e^{θ(t₀ - 3/4)}`, then
`Re W(f, f) ≤ -(3/8) A² + (5/4) S_Z B_d²`. -/
theorem re_W_testθ_le {ρ₀ : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes) {θ a : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {Kp : ℝ}
    (hKp2 : 2 ≤ Kp) (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp)
    (hηA : C.tiltDefect θ a ≤ Real.exp (θ * (C.t₀ - 3 / 4)) / 8) :
    (zetaZeroConfig.W (C.testθ θ a) (C.testθ θ a)).re ≤
      -(3 / 8) * Real.exp (θ * (C.t₀ - 3 / 4)) ^ 2 +
        (5 / 4) * zeroSumZ * (6 * coeffMass C.Q * C.tailDecay θ a Kp) ^ 2 := by
  classical
  obtain ⟨hC2, hcomp, -, -, -⟩ := C.testθ_properties hθ0 hθ hρ₀ a hKp2 hKp
  obtain ⟨-, hprod, -⟩ := C.K_spec
  have hKp0 : 0 ≤ Kp := by linarith
  set F : Finset zetaZeroConfig.carrier := C.nodes.image toCarrier with hF
  obtain ⟨Bd, hBd⟩ : ∃ x, x = 6 * coeffMass C.Q * C.tailDecay θ a Kp := ⟨_, rfl⟩
  have hcM := coeffMass_nonneg C.Q
  have hBd0 : 0 ≤ Bd := by rw [hBd]; exact mul_nonneg (by positivity) (C.tailDecay_nonneg θ a hKp0)
  have hKz : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F → paperFT C.K (gammaOf (ρ : ℂ)) = 0 := by
    intro ρ hρ
    have hdiv : divisorEval C.L (gammaOf (ρ : ℂ)) ≠ 0 := by
      refine C.divisorEval_ne_zero_of_not_node fun ν hν e => hρ ?_
      rw [hF, Finset.mem_image]
      exact ⟨ν, hν, Subtype.ext (gammaOf_injective e).symm⟩
    have h := hprod (gammaOf (ρ : ℂ))
    rw [riemannXiHat_gammaOf_eq_zero ρ.2] at h
    exact (mul_eq_zero.mp h).resolve_left hdiv
  have hstrip : ∀ ρ : zetaZeroConfig.carrier, |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := by
    intro ρ
    have h : IsNontrivialZero (ρ : ℂ) := ρ.2
    exact (WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le
  have hoff : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F →
      (1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖ ≤ Bd ∧
      (1 + |(ρ : ℂ).im|) ^ 2 *
        ‖paperFT (C.testθ θ a) ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤ Bd := by
    intro ρ hρ
    constructor
    · have h := C.testθ_off hθ0 hθ hρ₀ a hKp2 hKp (hstrip ρ) (hKz ρ hρ)
      rwa [WeilEF.gammaOf_re, ← hBd] at h
    · set ρr : zetaZeroConfig.carrier :=
        ⟨Zeta23.reflect (ρ : ℂ), zetaZeroConfig.reflect_mem (ρ : ℂ) ρ.2⟩ with hρr
      have hρrF : ρr ∉ F := by
        intro hmem
        rw [hF, Finset.mem_image] at hmem
        obtain ⟨ν, hν, hνe⟩ := hmem
        apply hρ
        rw [hF, Finset.mem_image]
        refine ⟨reflectSupport ν, C.reflect_mem_nodes hν, Subtype.ext ?_⟩
        have h1 : (ν : ℂ) = Zeta23.reflect (ρ : ℂ) := congrArg Subtype.val hνe
        change ((reflectSupport ν : XiDivisorSupport) : ℂ) = (ρ : ℂ)
        rw [reflectSupport_coe, h1, reflect_reflect]
      have hconj : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (ρr : ℂ) := by
        rw [hρr]; exact (gammaOf_reflect' _).symm
      have h := C.testθ_off hθ0 hθ hρ₀ a hKp2 hKp (hstrip ρr) (hKz ρr hρrF)
      rw [WeilEF.gammaOf_re, ← hBd] at h
      have him : (ρr : ℂ).im = (ρ : ℂ).im := by rw [hρr]; simp [Zeta23.reflect]
      rw [hconj, ← him]; exact h
  have hsplit := re_W_le_nodes_add_decay hC2 hcomp F hBd0 hoff
  have hsumF : ∑ ρ ∈ F, (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) ρ).re =
      ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re :=
    Finset.sum_image fun x _ y _ h => toCarrier_injective h
  rw [hsumF] at hsplit
  obtain ⟨A, hA⟩ : ∃ x, x = Real.exp (θ * (C.t₀ - 3 / 4)) := ⟨_, rfl⟩
  rw [← hA] at hηA ⊢
  have hA0 : 0 < A := by rw [hA]; exact Real.exp_pos _
  obtain ⟨ηt, hηt⟩ : ∃ x, x = C.tiltDefect θ a := ⟨_, rfl⟩
  rw [← hηt] at hηA
  have hηt0 : 0 ≤ ηt := by
    rw [hηt]; unfold tiltDefect; exact mul_nonneg (by positivity) (expTail_nonneg _ _ _)
  have hpair : ∀ ν ∈ C.nodes,
      (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re ≤
        (zetaZeroConfig.mult (toCarrier ν) : ℝ) * (-(3 / 8) * A ^ 2) := by
    intro ν hν
    obtain ⟨Y, hY, hYn⟩ := C.testθ_at_node hθ0 hθ a hν
    obtain ⟨Y', hY', hY'n⟩ := C.testθ_at_node hθ0 hθ a (C.reflect_mem_nodes hν)
    have hYn' : ‖Y‖ ≤ ηt := by rw [hηt]; exact hYn
    have hY'n' : ‖Y'‖ ≤ ηt := by rw [hηt]; exact hY'n
    set γ := gammaOf (ν : ℂ) with hγ
    set γ' := gammaOf (reflectSupport ν : ℂ) with hγ'
    have hγγ' : γ' = (starRingEnd ℂ) γ := by rw [hγ', hγ]; exact gammaOf_reflectSupport ν
    have hconj : (starRingEnd ℂ) (gammaOf ((toCarrier ν : zetaZeroConfig.carrier) : ℂ)) = γ' := by
      rw [hγγ']; rfl
    have hγc : gammaOf ((toCarrier ν : zetaZeroConfig.carrier) : ℂ) = γ := rfl
    unfold ZeroConfig.Wsummand
    rw [hconj, hγc, hY, hY']
    set Aν := Real.exp (γ.re * θ) with hAν
    have hre' : γ'.re = γ.re := by rw [hγγ', Complex.conj_re]
    have he : ‖cexp (γ * θ)‖ = Aν := by
      rw [Complex.norm_exp, hAν]; congr 1; simp
    have he' : ‖cexp (γ' * θ)‖ = Aν := by
      rw [Complex.norm_exp, hAν, ← hre']; congr 1; simp
    have hmain : (cexp (γ * θ) * (starRingEnd ℂ) (cexp (γ' * θ)) *
        (sgn ν * (starRingEnd ℂ) (sgn (reflectSupport ν)))).re ≤ -(2 / 3) * Aν ^ 2 := by
      rw [C.sgn_mul_conj_sgn_reflect hν]
      have hc : (starRingEnd ℂ) (cexp (γ' * θ)) = cexp (γ * θ) := by
        rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, hγγ', Complex.conj_conj]
      rw [hc]
      have h := re_neg_cexp_two_mul_le hθ0 hθ (γ := γ) (abs_gammaOf_divisorSupport_im_lt ν).le
      have e : cexp (γ * θ) * cexp (γ * θ) * -1 = -(cexp (γ * θ) * cexp (γ * θ)) := by ring
      rw [e]
      have hAν' : Real.exp (θ * γ.re) = Aν := by rw [hAν, mul_comm]
      rw [hAν'] at h
      exact h
    have hAle : A ≤ Aν := by
      rw [hA, hAν]
      apply Real.exp_le_exp.mpr
      have hc := (C.node_coords hν).1
      have hγre : γ.re = (ν : ℂ).im := WeilEF.gammaOf_re _
      have hX := C.hX2
      have h1 : C.t₀ - 3 / 4 ≤ γ.re := by
        rw [hγre]; have := abs_lt.mp (lt_of_lt_of_le hc hX)
        linarith [this.1]
      nlinarith
    have hηAν : ηt ≤ Aν / 8 := hηA.trans (by linarith)
    have hpairle := re_tilted_node_pair_le (norm_sgn ν) (norm_sgn (reflectSupport ν)) he he'
      hmain hYn' hY'n' hηt0 hηAν
    have e : (zetaZeroConfig.mult (toCarrier ν) : ℂ) * (cexp (γ * θ) * sgn ν - Y) *
        (starRingEnd ℂ) (cexp (γ' * θ) * sgn (reflectSupport ν) - Y') =
        ((zetaZeroConfig.mult (toCarrier ν) : ℝ) : ℂ) * ((cexp (γ * θ) * sgn ν - Y) *
          (starRingEnd ℂ) (cexp (γ' * θ) * sgn (reflectSupport ν) - Y')) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine hpairle.trans ?_
    have : A ^ 2 ≤ Aν ^ 2 := pow_le_pow_left₀ hA0.le hAle 2
    linarith
  have hblock : ∑ ν ∈ C.nodes,
      (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re ≤
        -(3 / 8) * A ^ 2 := by
    rw [← Finset.add_sum_erase _ _ hρ₀]
    have h1 := hpair ρ₀ hρ₀
    have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (toCarrier ρ₀) := by
      exact_mod_cast zetaZeroConfig.one_le_mult _ (toCarrier ρ₀).2
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg _
    have h2 : ∑ ν ∈ C.nodes.erase ρ₀,
        (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re ≤ 0 := by
      refine Finset.sum_nonpos fun ν hν => (hpair ν (Finset.mem_of_mem_erase hν)).trans ?_
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith only [hA2])
    have h3 := mul_le_mul_of_nonneg_right hm hA2
    linarith only [h1, h2, h3]
  rw [← hBd]
  linarith only [hsplit, hblock]


/-- Off the nodes, both evaluation points of the tilted test see only the decaying tail. -/
theorem testθ_off_carrier {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : XiDivisorSupport}
    (hρ₀ : ρ₀ ∈ C.nodes) (a : ℝ) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp)
    (ρ : zetaZeroConfig.carrier) (hρ : ρ ∉ C.nodes.image toCarrier) :
    (1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖ ≤
        6 * coeffMass C.Q * C.tailDecay θ a Kp ∧
      (1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT (C.testθ θ a) ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤
        6 * coeffMass C.Q * C.tailDecay θ a Kp := by
  classical
  obtain ⟨-, hprod, -⟩ := C.K_spec
  have hKz : ∀ σ : zetaZeroConfig.carrier, σ ∉ C.nodes.image toCarrier →
      paperFT C.K (gammaOf (σ : ℂ)) = 0 := by
    intro σ hσ
    have hdiv : divisorEval C.L (gammaOf (σ : ℂ)) ≠ 0 := by
      refine C.divisorEval_ne_zero_of_not_node fun ν hν e => hσ ?_
      rw [Finset.mem_image]
      exact ⟨ν, hν, Subtype.ext (gammaOf_injective e).symm⟩
    have h := hprod (gammaOf (σ : ℂ))
    rw [riemannXiHat_gammaOf_eq_zero σ.2] at h
    exact (mul_eq_zero.mp h).resolve_left hdiv
  have hstrip : ∀ σ : zetaZeroConfig.carrier, |(gammaOf (σ : ℂ)).im| ≤ 1 / 2 := by
    intro σ
    have h : IsNontrivialZero (σ : ℂ) := σ.2
    exact (WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le
  constructor
  · have h := C.testθ_off hθ0 hθ hρ₀ a hKp2 hKp (hstrip ρ) (hKz ρ hρ)
    rwa [WeilEF.gammaOf_re] at h
  · set ρr : zetaZeroConfig.carrier :=
      ⟨Zeta23.reflect (ρ : ℂ), zetaZeroConfig.reflect_mem (ρ : ℂ) ρ.2⟩ with hρr
    have hρrF : ρr ∉ C.nodes.image toCarrier := by
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨ν, hν, hνe⟩ := hmem
      apply hρ
      rw [Finset.mem_image]
      refine ⟨reflectSupport ν, C.reflect_mem_nodes hν, Subtype.ext ?_⟩
      have h1 : (ν : ℂ) = Zeta23.reflect (ρ : ℂ) := congrArg Subtype.val hνe
      change ((reflectSupport ν : XiDivisorSupport) : ℂ) = (ρ : ℂ)
      rw [reflectSupport_coe, h1, reflect_reflect]
    have hconj : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (ρr : ℂ) := by
      rw [hρr]; exact (gammaOf_reflect' _).symm
    have h := C.testθ_off hθ0 hθ hρ₀ a hKp2 hKp (hstrip ρr) (hKz ρr hρrF)
    rw [WeilEF.gammaOf_re] at h
    have him : (ρr : ℂ).im = (ρ : ℂ).im := by rw [hρr]; simp [Zeta23.reflect]
    rw [hconj, ← him]; exact h

end ClusterSetup

/-- **Cross term of two tilted cluster tests.** For cluster setups at heights at least `3/2`
apart, `‖W(f, f')‖ ≤ (5/4) S_Z (V B' + V' B + B B')`, with `V = e^{θ(t₀+3/4)} + η` the node size
and `B = 6 Σ|c_k| tailDecay` the tail constant of each test. -/
theorem norm_W_tilted_tests_le (C C' : ClusterSetup) (hsep : 3 / 2 ≤ |C.t₀ - C'.t₀|)
    {ρ₀ ρ₀' : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes) (hρ₀' : ρ₀' ∈ C'.nodes) {θ a : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    ‖zetaZeroConfig.W (C.testθ θ a) (C'.testθ θ a)‖ ≤ (5 / 4) * zeroSumZ *
      ((Real.exp (θ * (C.t₀ + 3 / 4)) + C.tiltDefect θ a) *
          (6 * coeffMass C'.Q * C'.tailDecay θ a Kp) +
        (Real.exp (θ * (C'.t₀ + 3 / 4)) + C'.tiltDefect θ a) *
          (6 * coeffMass C.Q * C.tailDecay θ a Kp) +
        (6 * coeffMass C.Q * C.tailDecay θ a Kp) * (6 * coeffMass C'.Q * C'.tailDecay θ a Kp)) := by
  classical
  have hKp0 : 0 ≤ Kp := by linarith
  set V := Real.exp (θ * (C.t₀ + 3 / 4)) + C.tiltDefect θ a with hV
  set V' := Real.exp (θ * (C'.t₀ + 3 / 4)) + C'.tiltDefect θ a with hV'
  set B := 6 * coeffMass C.Q * C.tailDecay θ a Kp with hB
  set B' := 6 * coeffMass C'.Q * C'.tailDecay θ a Kp with hB'
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) (coeffMass_nonneg _))
    (C.tailDecay_nonneg θ a hKp0)
  have hB'0 : 0 ≤ B' := mul_nonneg (mul_nonneg (by norm_num) (coeffMass_nonneg _))
    (C'.tailDecay_nonneg θ a hKp0)
  have hV0 : 0 ≤ V := by
    rw [hV]; exact add_nonneg (Real.exp_pos _).le (C.tiltDefect_nonneg θ a)
  have hV'0 : 0 ≤ V' := by
    rw [hV']; exact add_nonneg (Real.exp_pos _).le (C'.tiltDefect_nonneg θ a)
  have hdisj : ∀ ν, ν ∈ C.nodes → ν ∉ C'.nodes := by
    intro ν h h'
    have h1 := C.node_im_near h
    have h2 := C'.node_im_near h'
    have : |C.t₀ - C'.t₀| < 3 / 2 := by
      rw [abs_lt] at h1 h2 ⊢; constructor <;> linarith
    linarith
  set F := C.nodes.image ClusterSetup.toCarrier with hF
  set F' := C'.nodes.image ClusterSetup.toCarrier with hF'
  refine norm_W_le_of_pointwise (add_nonneg (add_nonneg (mul_nonneg hV0 hB'0)
    (mul_nonneg hV'0 hB0)) (mul_nonneg hB0 hB'0)) fun ρ => ?_
  have ht : 0 < (1 + |(ρ : ℂ).im|) ^ 2 := by positivity
  have ht1 : 1 ≤ (1 + |(ρ : ℂ).im|) ^ 2 := by nlinarith [abs_nonneg (ρ : ℂ).im]
  rw [le_div_iff₀ ht]
  by_cases hρ : ρ ∈ F
  · -- a node of the first setup
    rw [hF, Finset.mem_image] at hρ
    obtain ⟨ν, hν, rfl⟩ := hρ
    have hnode := C.norm_testθ_node_le hθ0 hθ a hν
    have hρF' : ClusterSetup.toCarrier ν ∉ F' := by
      rw [hF', Finset.mem_image]
      rintro ⟨μ, hμ, hμe⟩
      have : μ = ν := ClusterSetup.toCarrier_injective hμe
      exact hdisj ν hν (this ▸ hμ)
    obtain ⟨-, h2⟩ := C'.testθ_off_carrier hθ0 hθ hρ₀' a hKp2 hKp _ hρF'
    have hn1 := norm_nonneg (paperFT (C'.testθ θ a)
      ((starRingEnd ℂ) (gammaOf ((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ))))
    calc ‖paperFT (C.testθ θ a) (gammaOf ((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ))‖ *
          ‖paperFT (C'.testθ θ a)
            ((starRingEnd ℂ) (gammaOf ((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ)))‖ *
          (1 + |((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ).im|) ^ 2
        = ‖paperFT (C.testθ θ a) (gammaOf ((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ))‖ *
          ((1 + |((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ).im|) ^ 2 *
            ‖paperFT (C'.testθ θ a)
              ((starRingEnd ℂ) (gammaOf ((ClusterSetup.toCarrier ν : zetaZeroConfig.carrier) : ℂ)))‖) := by
          ring
      _ ≤ V * B' := mul_le_mul hnode h2 (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hV0
      _ ≤ V * B' + V' * B + B * B' := by
          have := mul_nonneg hV'0 hB0; have := mul_nonneg hB0 hB'0; linarith
  · obtain ⟨h1, -⟩ := C.testθ_off_carrier hθ0 hθ hρ₀ a hKp2 hKp ρ hρ
    by_cases hρ' : ρ ∈ F'
    · rw [hF', Finset.mem_image] at hρ'
      obtain ⟨ν, hν, hνe⟩ := hρ'
      have hc : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (reflectSupport ν : ℂ) := by
        rw [gammaOf_reflectSupport, ← hνe]; rfl
      have hnode := C'.norm_testθ_node_le hθ0 hθ a (C'.reflect_mem_nodes hν)
      rw [hc]
      calc ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖ *
            ‖paperFT (C'.testθ θ a) (gammaOf (reflectSupport ν : ℂ))‖ * (1 + |(ρ : ℂ).im|) ^ 2
          = ((1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖) *
            ‖paperFT (C'.testθ θ a) (gammaOf (reflectSupport ν : ℂ))‖ := by ring
        _ ≤ B * V' := mul_le_mul h1 hnode (norm_nonneg _) hB0
        _ ≤ V * B' + V' * B + B * B' := by
            have := mul_nonneg hV0 hB'0; have := mul_nonneg hB0 hB'0; linarith
    · obtain ⟨-, h2⟩ := C'.testθ_off_carrier hθ0 hθ hρ₀' a hKp2 hKp ρ hρ'
      have hx := norm_nonneg (paperFT (C.testθ θ a) (gammaOf (ρ : ℂ)))
      have hy := norm_nonneg (paperFT (C'.testθ θ a) ((starRingEnd ℂ) (gammaOf (ρ : ℂ))))
      have hprod := mul_le_mul h1 h2 (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hB0
      calc ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖ *
            ‖paperFT (C'.testθ θ a) ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ * (1 + |(ρ : ℂ).im|) ^ 2
          ≤ ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖ *
            ‖paperFT (C'.testθ θ a) ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ *
              ((1 + |(ρ : ℂ).im|) ^ 2 * (1 + |(ρ : ℂ).im|) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (sq_nonneg _) ht1)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ((1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖) *
            ((1 + |(ρ : ℂ).im|) ^ 2 *
              ‖paperFT (C'.testθ θ a) ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖) := by ring
        _ ≤ B * B' := hprod
        _ ≤ V * B' + V' * B + B * B' := by
            have := mul_nonneg hV0 hB'0; have := mul_nonneg hV'0 hB0; linarith

namespace ClusterSetup

variable (C : ClusterSetup)

/-- The Hodge constant of the tilted test in explicit form. -/
theorem tiltBd_le (hne : C.nodes.Nonempty) {θ a : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hlam : 6 + 3 / 2 * (windowCount C.t₀ : ℝ) ≤
      2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))) :
    6 * coeffMass C.Q * C.tailDecay θ a Kp ≤ 96 * Kp * (Mt + 1) *
      (2 ^ windowCount C.t₀ * ((windowCount C.t₀ + 1) *
        interpBound C.t₀ C.δ₀ (windowCount C.t₀)) * (C.t₀ + 3) ^ 2 *
        (Real.exp ((6 + 3 / 2 * windowCount C.t₀) * (a - 3 / 8)) *
          Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))))) := by
  set W := windowCount C.t₀ with hWdef
  have hKp0 : 0 ≤ Kp := by linarith
  have hM := tiltedPhiTailConst_nonneg
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  have hcM0 := coeffMass_nonneg C.Q
  have hMi1 : 1 ≤ Mi := by rw [hMidef]; exact C.one_le_interpBound
  have hsh : a - 1 / 4 - OffLinePairData.sh = a - 3 / 8 := by unfold OffLinePairData.sh; ring
  obtain ⟨τ, hτdef⟩ : ∃ x, x = expTail (tiltedPhi θ) (1 / 2 + 3 / 2 * W) (a - 3 / 8) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ x, x = Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
      Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hτE : τ ≤ 2 * (Mt + 1) * E := by
    rw [hτdef]
    have h := expTail_tiltedPhi_le (c := 1 / 2 + 3 / 2 * W) (X := a - 3 / 8) hθ0 hθ
      (by positivity) (by linarith)
    have e : (1 / 2 + 3 / 2 * (W : ℝ) + 11 / 2) = 6 + 3 / 2 * W := by ring
    rw [e] at h
    refine h.trans ?_
    rw [hEdef]
    have hp : 0 ≤ Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))) := by positivity
    nlinarith
  have hτ0 : 0 ≤ τ := by rw [hτdef]; exact expTail_nonneg _ _ _
  obtain ⟨T, hTdef⟩ : ∃ x, x = (C.t₀ + 3) ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hdecay : C.tailDecay θ a Kp ≤ 8 * Kp * T * (2 ^ W * τ) := by
    unfold ClusterSetup.tailDecay
    rw [hsh, ← hτdef]
    have hs1 : (1 : ℝ) ≤ C.t₀ + 3 := by linarith [C.ht₀]
    have hs : 1 + (C.t₀ + 2) = C.t₀ + 3 := by ring
    rw [hs]
    obtain ⟨u, hu⟩ : ∃ x, x = C.t₀ + 3 := ⟨_, rfl⟩
    rw [← hu]
    rw [← hu] at hs1 hTdef
    have hss : u ≤ u ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hs1
    have hs2 : 2 ≤ u ^ 2 := by
      have : (104 : ℝ) ≤ u := by rw [hu]; linarith [C.ht₀]
      linarith only [hss, this]
    have h1 : 1 + Kp ≤ Kp * u ^ 2 := by
      have := mul_le_mul_of_nonneg_left hs2 hKp0
      linarith only [this, hKp2]
    have h2 : 2 * Kp * u ≤ 2 * Kp * u ^ 2 := mul_le_mul_of_nonneg_left hss (by linarith)
    have h3 : u ^ 2 ≤ Kp * u ^ 2 := le_mul_of_one_le_left (sq_nonneg _) (by linarith)
    have hin : (1 + Kp) + 2 * Kp * u + u ^ 2 ≤ 4 * Kp * u ^ 2 := by
      linarith only [h1, h2, h3]
    have hpw : (0 : ℝ) ≤ 2 ^ W * τ := by positivity
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hin
      (by norm_num : (0 : ℝ) ≤ 2)) hpw
    rw [hTdef]
    refine h4.trans (le_of_eq ?_); ring
  have hpw0 : (0 : ℝ) ≤ 2 ^ W := by positivity
  have s1 : C.tailDecay θ a Kp ≤ 8 * Kp * T * (2 ^ W * (2 * (Mt + 1) * E)) :=
    hdecay.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτE hpw0) (by positivity))
  have s2 : 6 * coeffMass C.Q * C.tailDecay θ a Kp ≤
      6 * ((W + 1) * Mi) * (8 * Kp * T * (2 ^ W * (2 * (Mt + 1) * E))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcM (by norm_num)) s1
      (C.tailDecay_nonneg θ a hKp0) (by positivity)
  refine s2.trans (le_of_eq ?_)
  rw [hMidef, hTdef, hEdef]; ring

/-- The norm constant of the tilted test in explicit form. -/
theorem tiltN12_le (hne : C.nodes.Nonempty) (θ : ℝ) {Kp : ℝ} (hKp0 : 0 ≤ Kp) :
    4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
        ((C.t₀ + 3) ^ 2 * C.tiltedSize θ) ≤
      10 * Kp * ((windowCount C.t₀ + 1) * interpBound C.t₀ C.δ₀ (windowCount C.t₀) *
        (C.t₀ + 3) ^ 2 * C.tiltedSize θ) := by
  set W := windowCount C.t₀ with hWdef
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  rw [← hMidef]
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  have hcM0 := coeffMass_nonneg C.Q
  have hcosh : 1 + Real.cosh (heightPolarShift C.t₀ / 2) ≤ 5 / 2 := by
    have := (heightPolarShift_mem C.ht₀).2
    have h := cosh_le_exp_abs (heightPolarShift C.t₀ / 2)
    rw [abs_of_pos (by linarith [(heightPolarShift_mem C.ht₀).1])] at h
    have h2 : Real.exp (heightPolarShift C.t₀ / 2) ≤ 3 / 2 :=
      (Real.exp_le_exp.mpr (by unfold OffLinePairData.sh; linarith)).trans
        OffLinePairData.exp_sh_half_le
    linarith
  have hch0 : 0 ≤ 1 + Real.cosh (heightPolarShift C.t₀ / 2) := by
    have := Real.cosh_pos (heightPolarShift C.t₀ / 2); linarith
  have hBθ0 := C.tiltedSize_nonneg θ
  have hMi0 : 0 ≤ Mi := by rw [hMidef]; linarith [C.one_le_interpBound]
  have h1 : coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2)) ≤ ((W + 1) * Mi) * (5 / 2) :=
    mul_le_mul hcM hcosh hch0 (by positivity)
  calc 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
        ((C.t₀ + 3) ^ 2 * C.tiltedSize θ)
      ≤ 4 * Kp * (((W + 1) * Mi) * (5 / 2)) * ((C.t₀ + 3) ^ 2 * C.tiltedSize θ) := by gcongr
    _ = 10 * Kp * ((W + 1) * Mi * (C.t₀ + 3) ^ 2 * C.tiltedSize θ) := by ring

end ClusterSetup

/-! ## The Landau-sharp inertia law -/

/-- The Hodge ratio of the tilted cluster test at `ρ`: its tail constant over its node size,
`2^N (N+1) M (t+3)² e^{(6+3N/2)X - π cos(2θ) e^{2X}} e^{-θ(t - 3/4)}`. -/
def tiltedHodgeRatio (θ a : ℝ) (ρ : ℂ) : ℝ :=
  2 ^ windowCount ρ.im * ((windowCount ρ.im + 1) *
    ClusterSetup.interpBound ρ.im (ρ.re - 1 / 2) (windowCount ρ.im)) * (ρ.im + 3) ^ 2 *
    (Real.exp ((6 + 3 / 2 * windowCount ρ.im) * (a - 3 / 8)) *
      Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))))) *
    Real.exp (-(θ * (ρ.im - 3 / 4)))

/-- The norm ratio of the tilted cluster test at `ρ`: `(N+1) M (t+3)² B_θ e^{-θ(t - 3/4)}`. -/
def tiltedNormRatio (θ : ℝ) (ρ : ℂ) : ℝ :=
  (windowCount ρ.im + 1) * ClusterSetup.interpBound ρ.im (ρ.re - 1 / 2) (windowCount ρ.im) *
    (ρ.im + 3) ^ 2 * (2 ^ windowCount ρ.im * expTail (tiltedPhi θ) (3 / 2 * windowCount ρ.im) 0) *
    Real.exp (-(θ * (ρ.im - 3 / 4)))

theorem exp_mul_exp_neg_self (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- **The Landau-sharp inertia law.** There are absolute constants `K₀, K₁` with the following
property. For every tilt `0 ≤ θ < π/4` and level `a ≥ 1`, let `T` be a finite set of zeros
`β + it` of `ζ` with `β > ½`, `t ≥ 101`, ordinates pairwise at least `3/2` apart, each satisfying
`6 + 3N/2 ≤ 2π cos(2θ) e^{2X}`, with `tiltedHodgeRatio ≤ R` and `tiltedNormRatio ≤ Λ`. If
`K₀ |T| R ≤ 1`, then

`|T| ≤ weilNegIndex ζ a (1/(K₁ a |T| (Λ² + 1)))`.

The condition `K₀ |T| R ≤ 1` is the Landau horizon `(π sin 2ε/ε) e^{2X}` with a `log|T|` margin,
`ε = π/4 - θ`. The margin `Λ` is `e^{ε t}` times `(N/cos 2θ)^{O(N)}` and polylogarithmic factors.
With `ε ≍ (log² t + log t log 1/δ)/t`, every separated off-line zero below
`2π e^{2a-3/4}/(1+κ)` (`κ > 0` fixed) is a negative square of margin
`exp(-O_κ(log² t + log t log 1/δ))`. -/
theorem weilNegIndex_ge_card_tilted :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {θ a R Λ : ℝ} (T : Finset ℂ), 0 ≤ θ → 2 * θ < π / 2 →
      1 ≤ a →
      (∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re ∧ 101 ≤ ρ.im ∧
        6 + 3 / 2 * (windowCount ρ.im : ℝ) ≤
          2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) ∧
        tiltedHodgeRatio θ a ρ ≤ R ∧ tiltedNormRatio θ ρ ≤ Λ) →
      (∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 3 / 2 ≤ |ρ.im - σ.im|) →
      K₀ * T.card * R ≤ 1 →
      T.card ≤ weilNegIndex zetaZeroConfig a (1 / (K₁ * a * T.card * (Λ ^ 2 + 1))) := by
  obtain ⟨Kp, hKp2, hKp⟩ := OffLinePairData.exists_plateau_constant
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hupper := zeta_weil_negative_index_le_of_local_count hA₀ hloc
  have hS := zeroSumZ_nonneg
  have hM := tiltedPhiTailConst_nonneg
  have hKp0 : 0 ≤ Kp := by linarith
  obtain ⟨KB, hKB⟩ : ∃ x, x = 96 * Kp * (Mt + 1) := ⟨_, rfl⟩
  have hKB0 : 0 < KB := by rw [hKB]; have : 0 < Kp := by linarith
                           positivity
  obtain ⟨S, hSdef⟩ : ∃ x, x = zeroSumZ := ⟨_, rfl⟩
  rw [← hSdef] at hS
  refine ⟨200 * (S + 1) * KB + 4 * KB, 1600 * Kp ^ 2, by positivity,
    mul_pos (by norm_num) (pow_pos (by linarith) 2), ?_⟩
  intro θ a R Λ T hθ0 hθ ha hT hsep hK
  classical
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simp
  have ha0 : 0 ≤ a := by linarith
  have hn1 : (1 : ℝ) ≤ T.card := by exact_mod_cast hTne.card_pos
  have hex : ∀ i : T, ∃ C : ClusterSetup, C.t₀ = (i : ℂ).im ∧ C.δ₀ = (i : ℂ).re - 1 / 2 ∧
      ∃ ν ∈ C.nodes, (ν : ℂ) = i := fun i =>
    exists_clusterSetup_node (hT i i.2).1 (hT i i.2).2.1 (hT i i.2).2.2.1
  choose Cs hCt hCδ ν hνm hνe using hex
  have hne : ∀ i, (Cs i).nodes.Nonempty := fun i => ⟨ν i, hνm i⟩
  have hWt : ∀ i : T, windowCount (Cs i).t₀ = windowCount (i : ℂ).im := fun i => by rw [hCt i]
  -- `R ≥ 0`, `Λ ≥ 0`
  obtain ⟨ρ₁, hρ₁⟩ := hTne
  have hR0 : 0 ≤ R := by
    refine le_trans ?_ (hT ρ₁ hρ₁).2.2.2.2.1
    unfold tiltedHodgeRatio
    have hMi : 0 ≤ ClusterSetup.interpBound ρ₁.im (ρ₁.re - 1 / 2) (windowCount ρ₁.im) := by
      have hδ : 0 < ρ₁.re - 1 / 2 := by linarith [(hT ρ₁ hρ₁).2.1]
      unfold ClusterSetup.interpBound; have := Real.exp_pos 1; positivity
    have ht3 : (0 : ℝ) ≤ ρ₁.im + 3 := by linarith [(hT ρ₁ hρ₁).2.2.1]
    positivity
  have hΛ0 : 0 ≤ Λ := by
    refine le_trans ?_ (hT ρ₁ hρ₁).2.2.2.2.2
    unfold tiltedNormRatio
    have hMi : 0 ≤ ClusterSetup.interpBound ρ₁.im (ρ₁.re - 1 / 2) (windowCount ρ₁.im) := by
      have hδ : 0 < ρ₁.re - 1 / 2 := by linarith [(hT ρ₁ hρ₁).2.1]
      unfold ClusterSetup.interpBound; have := Real.exp_pos 1; positivity
    have ht3 : (0 : ℝ) ≤ ρ₁.im + 3 := by linarith [(hT ρ₁ hρ₁).2.2.1]
    have := expTail_nonneg (tiltedPhi θ) (3 / 2 * windowCount ρ₁.im) 0
    positivity
  set n : ℝ := (T.card : ℝ) with hn
  -- the smallness of `r = K_B R`
  obtain ⟨r, hrdef⟩ : ∃ x, x = KB * R := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hrdef]; exact mul_nonneg hKB0.le hR0
  have hKr : (200 * (S + 1) * n + 4 * n) * r ≤ 1 := by
    have e : (200 * (S + 1) * KB + 4 * KB) * n * R = (200 * (S + 1) * n + 4 * n) * r := by
      rw [hrdef]; ring
    rw [← e]; exact hK
  have hr4 : r ≤ 1 / 4 := by
    have h1 : 4 * r ≤ (200 * (S + 1) * n + 4 * n) * r := by
      apply mul_le_mul_of_nonneg_right _ hr0
      have : 0 ≤ 200 * (S + 1) * n := by positivity
      linarith
    linarith
  have hr1 : r ≤ 1 := by linarith
  -- per-zero quantities
  set A : T → ℝ := fun i => Real.exp (θ * ((Cs i).t₀ - 3 / 4)) with hAdef
  have hA0 : ∀ i, 0 < A i := fun i => Real.exp_pos _
  have hBd : ∀ i : T, 6 * coeffMass (Cs i).Q * (Cs i).tailDecay θ a Kp ≤ r * A i := by
    intro i
    obtain ⟨-, -, -, h4, h5, -⟩ := hT i i.2
    have hlam : 6 + 3 / 2 * (windowCount (Cs i).t₀ : ℝ) ≤
        2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) := by rw [hWt]; exact h4
    have h := (Cs i).tiltBd_le (hne i) hθ0 hθ hKp2 hlam
    rw [← hKB] at h
    have hratio : tiltedHodgeRatio θ a (i : ℂ) * A i =
        2 ^ windowCount (Cs i).t₀ * ((windowCount (Cs i).t₀ + 1) *
          ClusterSetup.interpBound (Cs i).t₀ (Cs i).δ₀ (windowCount (Cs i).t₀)) *
          ((Cs i).t₀ + 3) ^ 2 * (Real.exp ((6 + 3 / 2 * windowCount (Cs i).t₀) * (a - 3 / 8)) *
            Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))))) := by
      unfold tiltedHodgeRatio
      simp only [hAdef]
      rw [hWt, hCt, hCδ]
      rw [mul_assoc _ (Real.exp _) (Real.exp _), mul_comm (Real.exp (-(θ * _))),
        exp_mul_exp_neg_self, mul_one]
    rw [← hratio] at h
    have := mul_le_mul_of_nonneg_right h5 (hA0 i).le
    calc 6 * coeffMass (Cs i).Q * (Cs i).tailDecay θ a Kp
        ≤ KB * (tiltedHodgeRatio θ a (i : ℂ) * A i) := h
      _ ≤ KB * (R * A i) := mul_le_mul_of_nonneg_left this hKB0.le
      _ = r * A i := by rw [hrdef]; ring
  have hN12 : ∀ i : T, 4 * Kp * (coeffMass (Cs i).Q *
      (1 + Real.cosh (heightPolarShift (Cs i).t₀ / 2))) *
        (((Cs i).t₀ + 3) ^ 2 * (Cs i).tiltedSize θ) ≤ 10 * Kp * Λ * A i := by
    intro i
    have h := (Cs i).tiltN12_le (hne i) θ hKp0
    have h6 := (hT i i.2).2.2.2.2.2
    have hratio : tiltedNormRatio θ (i : ℂ) * A i =
        (windowCount (Cs i).t₀ + 1) * ClusterSetup.interpBound (Cs i).t₀ (Cs i).δ₀
          (windowCount (Cs i).t₀) * ((Cs i).t₀ + 3) ^ 2 * (Cs i).tiltedSize θ := by
      unfold tiltedNormRatio ClusterSetup.tiltedSize
      simp only [hAdef]
      rw [hWt, hCt, hCδ]
      rw [mul_assoc _ (Real.exp _) (Real.exp _), mul_comm (Real.exp (-(θ * _))),
        exp_mul_exp_neg_self, mul_one]
    rw [← hratio] at h
    have := mul_le_mul_of_nonneg_right h6 (hA0 i).le
    calc _ ≤ 10 * Kp * (tiltedNormRatio θ (i : ℂ) * A i) := h
      _ ≤ 10 * Kp * (Λ * A i) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 10 * Kp * Λ * A i := by ring
  have hprop := fun i : T => (Cs i).testθ_properties hθ0 hθ (hνm i) a hKp2 hKp
  -- the normalized tests
  set c : T → ℂ := fun i => (((A i)⁻¹ : ℝ) : ℂ) with hcdef
  set g : T → ℝ → ℂ := fun i u => c i * (Cs i).testθ θ a u with hgdef
  have hcn : ∀ i, ‖c i‖ = (A i)⁻¹ := fun i => by
    simp only [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hA0 i))]
  have hcc : ∀ i, c i * (starRingEnd ℂ) (c i) = (((A i)⁻¹ ^ 2 : ℝ) : ℂ) := fun i => by
    simp only [hcdef, Complex.conj_ofReal]; push_cast; ring
  -- the diagonal
  set D : ℝ := (5 / 4) * S * r ^ 2 with hD
  have hdiag : ∀ i : T, (zetaZeroConfig.W (g i) (g i)).re ≤ -(3 / 8) + D := by
    intro i
    have hηA : (Cs i).tiltDefect θ a ≤ A i / 8 := by
      have h1 := (Cs i).tiltDefect_le hθ0 hθ (hνm i) a hKp0
      have h2 := hBd i
      have h3 : r * A i ≤ A i / 4 := by
        have := mul_le_mul_of_nonneg_right hr4 (hA0 i).le; linarith
      linarith
    have hW := (Cs i).re_W_testθ_le (hνm i) hθ0 hθ hKp2 hKp hηA
    rw [← hSdef] at hW
    have hB0 : 0 ≤ 6 * coeffMass (Cs i).Q * (Cs i).tailDecay θ a Kp :=
      mul_nonneg (mul_nonneg (by norm_num) (coeffMass_nonneg _)) ((Cs i).tailDecay_nonneg θ a hKp0)
    have hBsq := pow_le_pow_left₀ hB0 (hBd i) 2
    have hgi : zetaZeroConfig.W (g i) (g i) =
        (((A i)⁻¹ ^ 2 : ℝ) : ℂ) * zetaZeroConfig.W ((Cs i).testθ θ a) ((Cs i).testθ θ a) := by
      rw [hgdef, W_const_mul, hcc]
    rw [hgi, Complex.re_ofReal_mul]
    have hAi := hA0 i
    obtain ⟨w, hw⟩ : ∃ x, x = (zetaZeroConfig.W ((Cs i).testθ θ a) ((Cs i).testθ θ a)).re :=
      ⟨_, rfl⟩
    rw [← hw] at hW ⊢
    have hW' : w ≤ -(3 / 8) * A i ^ 2 + (5 / 4) * S * (r * A i) ^ 2 := by
      have : (5 / 4) * S * (6 * coeffMass (Cs i).Q * (Cs i).tailDecay θ a Kp) ^ 2 ≤
          (5 / 4) * S * (r * A i) ^ 2 := mul_le_mul_of_nonneg_left hBsq (by positivity)
      linarith
    have hinv : (A i)⁻¹ ^ 2 * A i ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hAi.ne', one_pow]
    have hpos : 0 ≤ (A i)⁻¹ ^ 2 := sq_nonneg _
    calc (A i)⁻¹ ^ 2 * w ≤ (A i)⁻¹ ^ 2 * (-(3 / 8) * A i ^ 2 + (5 / 4) * S * (r * A i) ^ 2) :=
          mul_le_mul_of_nonneg_left hW' hpos
      _ = -(3 / 8) * ((A i)⁻¹ ^ 2 * A i ^ 2) + (5 / 4) * S * r ^ 2 * ((A i)⁻¹ ^ 2 * A i ^ 2) := by
          ring
      _ = -(3 / 8) + D := by rw [hinv, hD]; ring
  -- the cross terms
  set O : ℝ := (5 / 4) * S * (17 * r) with hO
  have he2 : Real.exp (3 / 2 * θ) ≤ 7 := by
    have h1 : Real.exp (3 / 2 * θ) ≤ Real.exp (1 + 1 / 5) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_lt_d2])
    have h2 : Real.exp (1 + 1 / 5) = Real.exp 1 * Real.exp (1 / 5) := Real.exp_add _ _
    have h3 := Real.exp_one_lt_d9
    have h4 : Real.exp (1 / 5) ≤ 5 / 4 := by
      have h := Real.add_one_le_exp (-(1 / 5))
      have hp := Real.exp_pos (1 / 5)
      have e : Real.exp (-(1 / 5)) = (Real.exp (1 / 5))⁻¹ := Real.exp_neg _
      rw [e] at h
      have : (4 : ℝ) / 5 ≤ (Real.exp (1 / 5))⁻¹ := by linarith
      have h5 := (le_inv_comm₀ (by norm_num) hp).mp this
      linarith [h5]
    have h5 : Real.exp 1 * Real.exp (1 / 5) ≤ 2.7182818286 * (5 / 4) :=
      mul_le_mul h3.le h4 (Real.exp_pos _).le (by norm_num)
    linarith
  have hV : ∀ i : T, Real.exp (θ * ((Cs i).t₀ + 3 / 4)) + (Cs i).tiltDefect θ a ≤ 8 * A i := by
    intro i
    have h1 : Real.exp (θ * ((Cs i).t₀ + 3 / 4)) = Real.exp (3 / 2 * θ) * A i := by
      simp only [hAdef]; rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (3 / 2 * θ) * A i ≤ 7 * A i := mul_le_mul_of_nonneg_right he2 (hA0 i).le
    have h3 := (Cs i).tiltDefect_le hθ0 hθ (hνm i) a hKp0
    have h4 := hBd i
    have h5 : r * A i ≤ A i := by
      have := mul_le_mul_of_nonneg_right hr1 (hA0 i).le; linarith only [this]
    have hA := (hA0 i).le
    rw [h1]
    linarith only [h2, h3, h4, h5, hA]
  have hoff : ∀ i j : T, i ≠ j → ‖zetaZeroConfig.W (g i) (g j)‖ ≤ O := by
    intro i j hij
    have hsep' : 3 / 2 ≤ |(Cs i).t₀ - (Cs j).t₀| := by
      rw [hCt, hCt]; exact hsep i i.2 j j.2 fun h => hij (Subtype.ext h)
    have h := norm_W_tilted_tests_le (Cs i) (Cs j) hsep' (hνm i) (hνm j) hθ0 hθ (a := a) hKp2 hKp
    rw [← hSdef] at h
    have hgij : zetaZeroConfig.W (g i) (g j) = c i * (starRingEnd ℂ) (c j) *
        zetaZeroConfig.W ((Cs i).testθ θ a) ((Cs j).testθ θ a) := by rw [hgdef, W_const_mul]
    rw [hgij, norm_mul, norm_mul, RCLike.norm_conj, hcn, hcn]
    have hBi := hBd i
    have hBj := hBd j
    have hVi := hV i
    have hVj := hV j
    have hBi0 : 0 ≤ 6 * coeffMass (Cs i).Q * (Cs i).tailDecay θ a Kp :=
      mul_nonneg (mul_nonneg (by norm_num) (coeffMass_nonneg _)) ((Cs i).tailDecay_nonneg θ a hKp0)
    have hBj0 : 0 ≤ 6 * coeffMass (Cs j).Q * (Cs j).tailDecay θ a Kp :=
      mul_nonneg (mul_nonneg (by norm_num) (coeffMass_nonneg _)) ((Cs j).tailDecay_nonneg θ a hKp0)
    have hVi0 : 0 ≤ Real.exp (θ * ((Cs i).t₀ + 3 / 4)) + (Cs i).tiltDefect θ a :=
      add_nonneg (Real.exp_pos _).le ((Cs i).tiltDefect_nonneg θ a)
    have hVj0 : 0 ≤ Real.exp (θ * ((Cs j).t₀ + 3 / 4)) + (Cs j).tiltDefect θ a :=
      add_nonneg (Real.exp_pos _).le ((Cs j).tiltDefect_nonneg θ a)
    obtain ⟨Vi, hVid⟩ : ∃ x, x = Real.exp (θ * ((Cs i).t₀ + 3 / 4)) + (Cs i).tiltDefect θ a :=
      ⟨_, rfl⟩
    obtain ⟨Vj, hVjd⟩ : ∃ x, x = Real.exp (θ * ((Cs j).t₀ + 3 / 4)) + (Cs j).tiltDefect θ a :=
      ⟨_, rfl⟩
    obtain ⟨Bi, hBid⟩ : ∃ x, x = 6 * coeffMass (Cs i).Q * (Cs i).tailDecay θ a Kp := ⟨_, rfl⟩
    obtain ⟨Bj, hBjd⟩ : ∃ x, x = 6 * coeffMass (Cs j).Q * (Cs j).tailDecay θ a Kp := ⟨_, rfl⟩
    rw [← hVid, ← hVjd, ← hBid, ← hBjd] at h
    rw [← hVid] at hVi hVi0; rw [← hVjd] at hVj hVj0
    rw [← hBid] at hBi hBi0; rw [← hBjd] at hBj hBj0
    have hAi := hA0 i
    have hAj := hA0 j
    obtain ⟨w, hw⟩ : ∃ x, x = ‖zetaZeroConfig.W ((Cs i).testθ θ a) ((Cs j).testθ θ a)‖ := ⟨_, rfl⟩
    rw [← hw] at h ⊢
    have hsum : Vi * Bj + Vj * Bi + Bi * Bj ≤ 17 * r * (A i * A j) := by
      have e1 : Vi * Bj ≤ (8 * A i) * (r * A j) :=
        mul_le_mul hVi hBj hBj0 (by linarith only [hAi])
      have e2 : Vj * Bi ≤ (8 * A j) * (r * A i) :=
        mul_le_mul hVj hBi hBi0 (by linarith only [hAj])
      have e3 : Bi * Bj ≤ (r * A i) * (r * A j) :=
        mul_le_mul hBi hBj hBj0 (mul_nonneg hr0 hAi.le)
      have hrr : r * r ≤ r := mul_le_of_le_one_left hr0 hr1
      have e4 : (r * r) * (A i * A j) ≤ r * (A i * A j) :=
        mul_le_mul_of_nonneg_right hrr (mul_pos hAi hAj).le
      have e5 : (r * A i) * (r * A j) = (r * r) * (A i * A j) := by ring
      have e6 : (8 * A i) * (r * A j) = 8 * (r * (A i * A j)) := by ring
      have e7 : (8 * A j) * (r * A i) = 8 * (r * (A i * A j)) := by ring
      have e8 : 17 * r * (A i * A j) = 17 * (r * (A i * A j)) := by ring
      rw [e8]
      linarith only [e1, e2, e3, e4, e5, e6, e7]
    have hw' : w ≤ (5 / 4) * S * (17 * r * (A i * A j)) :=
      h.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hS))
    have hinv : (A i)⁻¹ * (A j)⁻¹ * (A i * A j) = 1 := by
      rw [mul_mul_mul_comm, inv_mul_cancel₀ hAi.ne', inv_mul_cancel₀ hAj.ne', one_mul]
    calc (A i)⁻¹ * (A j)⁻¹ * w ≤ (A i)⁻¹ * (A j)⁻¹ * ((5 / 4) * S * (17 * r * (A i * A j))) :=
          mul_le_mul_of_nonneg_left hw'
            (mul_nonneg (inv_nonneg.mpr hAi.le) (inv_nonneg.mpr hAj.le))
      _ = (5 / 4) * S * (17 * r) * ((A i)⁻¹ * (A j)⁻¹ * (A i * A j)) := by ring
      _ = O := by rw [hinv, hO]; ring
  have hO0 : 0 ≤ O := by rw [hO]; positivity
  have hDO : D + ((Fintype.card T : ℝ) - 1) * O ≤ 1 / 8 := by
    rw [Fintype.card_coe, ← hn, hD, hO]
    have h1 : S * r * n ≤ 1 / 200 := by
      have : 200 * (S * r * n) ≤ (200 * (S + 1) * n + 4 * n) * r := by nlinarith
      linarith
    have h2 : S * r ^ 2 ≤ S * r := by
      have : r ^ 2 ≤ r := by nlinarith
      exact mul_le_mul_of_nonneg_left this hS
    have h3 : S * r ≤ S * r * n := le_mul_of_one_le_right (mul_nonneg hS hr0) hn1
    nlinarith
  -- the `L²` sizes
  set M : ℝ := 200 * a * Kp ^ 2 * Λ ^ 2 with hMdef
  have hMi : ∀ i : T, ∫ u, ‖g i u‖ ^ 2 ≤ M := by
    intro i
    obtain ⟨hC2, -, -, -, -⟩ := hprop i
    have hsupp : ∀ u, (Cs i).testθ θ a u ≠ 0 → |u| ≤ a := by
      have hsp0 : 0 ≤ heightPolarShift (Cs i).t₀ := by
        linarith [(heightPolarShift_mem (Cs i).ht₀).1]
      exact clusterTest_supp (Cs i).κ_pos.le hsp0 ((Cs i).test_supp_bound a)
    have hN := (Cs i).testθ_norm hθ0 hθ (hνm i) a hKp2 hKp
    have hN' := hN.trans (hN12 i)
    have h := integral_norm_sq_le ha0 hC2 hsupp
    obtain ⟨A1, hA1⟩ : ∃ x, x = ∫ u, ‖(Cs i).testθ θ a u‖ := ⟨_, rfl⟩
    obtain ⟨A2, hA2⟩ : ∃ x, x = ∫ u, ‖deriv (deriv ((Cs i).testθ θ a)) u‖ := ⟨_, rfl⟩
    rw [← hA1, ← hA2] at h hN'
    have h1 : 0 ≤ A1 := by rw [hA1]; exact integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ A2 := by rw [hA2]; exact integral_nonneg fun _ => norm_nonneg _
    have hL0 : 0 ≤ 10 * Kp * Λ * A i := by have := hA0 i; positivity
    have h3 : A2 * A1 ≤ (10 * Kp * Λ * A i) ^ 2 := by
      have e : (A1 + A2) ^ 2 = A2 * A1 + (A1 ^ 2 + A1 * A2 + A2 ^ 2) := by ring
      have : A2 * A1 ≤ (A1 + A2) ^ 2 := by
        rw [e]
        exact le_add_of_nonneg_right
          (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg h1 h2)) (sq_nonneg _))
      exact this.trans (pow_le_pow_left₀ (add_nonneg h1 h2) hN' 2)
    have hfi : ∫ u, ‖(Cs i).testθ θ a u‖ ^ 2 ≤ 2 * a * (10 * Kp * Λ * A i) ^ 2 :=
      calc ∫ u, ‖(Cs i).testθ θ a u‖ ^ 2 ≤ 2 * a * A2 * A1 := h
        _ = 2 * a * (A2 * A1) := by ring
        _ ≤ 2 * a * (10 * Kp * Λ * A i) ^ 2 := mul_le_mul_of_nonneg_left h3 (by linarith)
    have hgi : (fun u => ‖g i u‖ ^ 2) = fun u => (A i)⁻¹ ^ 2 * ‖(Cs i).testθ θ a u‖ ^ 2 := by
      funext u; simp only [hgdef]; rw [norm_mul, hcn, mul_pow]
    rw [hgi, integral_const_mul]
    have hAi := hA0 i
    have hinv : (A i)⁻¹ ^ 2 * A i ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hAi.ne', one_pow]
    calc (A i)⁻¹ ^ 2 * ∫ u, ‖(Cs i).testθ θ a u‖ ^ 2
        ≤ (A i)⁻¹ ^ 2 * (2 * a * (10 * Kp * Λ * A i) ^ 2) :=
          mul_le_mul_of_nonneg_left hfi (sq_nonneg _)
      _ = 200 * a * Kp ^ 2 * Λ ^ 2 * ((A i)⁻¹ ^ 2 * A i ^ 2) := by ring
      _ = M := by rw [hinv, hMdef]; ring
  set ε : ℝ := 1 / (1600 * Kp ^ 2 * a * n * (Λ ^ 2 + 1)) with hε
  have hden : 0 < 1600 * Kp ^ 2 * a * n * (Λ ^ 2 + 1) := by
    have : 0 < Kp := by linarith
    have : 0 < n := by linarith
    have : 0 < a := by linarith
    positivity
  have hε0 : 0 < ε := by rw [hε]; exact one_div_pos.mpr hden
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one hden]
    have h1 : 1 ≤ Kp ^ 2 := one_le_pow₀ (by linarith only [hKp2])
    have h2 : 1 ≤ Λ ^ 2 + 1 := by have := sq_nonneg Λ; linarith only [this]
    have h3 : 1 ≤ Kp ^ 2 * a := one_le_mul_of_one_le_of_one_le h1 ha
    have h4 : 1 ≤ Kp ^ 2 * a * n := one_le_mul_of_one_le_of_one_le h3 hn1
    have h5 : 1 ≤ Kp ^ 2 * a * n * (Λ ^ 2 + 1) := one_le_mul_of_one_le_of_one_le h4 h2
    linarith only [h5]
  have hεM : ε * (Fintype.card T * M) ≤ 1 / 8 := by
    rw [Fintype.card_coe, ← hn, hε, hMdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
    have hl : Λ ^ 2 ≤ Λ ^ 2 + 1 := by linarith only
    have hpos : 0 ≤ n * (200 * a * Kp ^ 2) :=
      mul_nonneg (by linarith only [hn1]) (mul_nonneg (mul_nonneg (by norm_num) ha0) (sq_nonneg _))
    have e1 : n * (200 * a * Kp ^ 2 * Λ ^ 2) = n * (200 * a * Kp ^ 2) * Λ ^ 2 := by ring
    have e2 : 1 / 8 * (1600 * Kp ^ 2 * a * n * (Λ ^ 2 + 1)) =
        n * (200 * a * Kp ^ 2) * (Λ ^ 2 + 1) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_left hl hpos
  have hgC2 : ∀ i : T, ContDiff ℝ 2 (g i) := fun i =>
    contDiff_const.mul (hprop i).1
  have hgts : ∀ i : T, tsupport (g i) ⊆ Icc (-a) a := fun i =>
    (tsupport_mul_subset_right (f := fun _ : ℝ => c i)).trans (hprop i).2.2.1
  have hgp1 : ∀ i : T, paperFT (g i) (I / 2) = 0 := fun i => by
    simp only [hgdef]; rw [paperFT_const_mul, (hprop i).2.2.2.1, mul_zero]
  have hgp2 : ∀ i : T, paperFT (g i) (-(I / 2)) = 0 := fun i => by
    simp only [hgdef]; rw [paperFT_const_mul, (hprop i).2.2.2.2, mul_zero]
  obtain ⟨V, hVf, hdim, hVprop, hneg⟩ := exists_negative_subspace_of_gram (ι := T) g hgC2 hgts
    hgp1 hgp2 hdiag hoff hO0 hDO hMi hε0.le hεM
  have hbdd : BddAbove {m : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
      Module.finrank ℂ V = m ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)} := by
    refine ⟨(offLinePairsBelow zetaZeroConfig (inertiaHorizonHeight A₀ a ε)).card, ?_⟩
    rintro m ⟨W, hWf, rfl, hW, hWneg⟩
    exact hupper a ε (by linarith) hε0 hε1 W hWf hW hWneg
  have hmem : Module.finrank ℂ V ∈ {m : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ),
      FiniteDimensional ℂ V ∧ Module.finrank ℂ V = m ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)} :=
    ⟨V, hVf, rfl, hVprop, hneg⟩
  have hle := le_csSup hbdd hmem
  rw [hdim, Fintype.card_coe] at hle
  unfold weilNegIndex
  exact hle

end

end RHTower
