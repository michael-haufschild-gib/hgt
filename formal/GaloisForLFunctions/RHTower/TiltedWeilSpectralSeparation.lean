import GaloisForLFunctions.RHTower.TiltedClusterNyquistExclusion

/-!
# Landau-sharp spectral separation of the finite-level Weil form

Let `μ(a) ≥ -η` say that `Re W(f,f) ≥ -η ∫|f|²` for every polar-constrained `C²` test on
`[-a, a]` (`WeilFloorAtLevel`). `WeilFloorSpectralSeparation` shows that an off-line zero at height
`t` below `≈ 2e^{2a-3/4}` forces `μ(a) ≤ -e^{-πt/2 - polylog}`. This file replaces both constants
by their tilted values.

**Theorem** (`weilFloor_tilted_spectral_separation`). For every tilt `0 ≤ θ < π/4`,
`ε = π/4 - θ`, a zero `β₀ + it₀` with `β₀ > ½` below the Landau horizon of
`hodgeIndex_tilted_cluster_horizon` forces

`log(1/η) ≤ 2ε t₀ + O(log t₀ (log log t₀ + log 1/δ₀) + log B_θ + log a)`,

where `B_θ = 2^N ∫‖Φ(u + iθ)‖ e^{3N|u|/2}`. So `μ(a) ≥ -η` certifies RH up to
`min((π sin 2ε/ε) e^{2a-3/4}, (1/2ε) log(1/η))`, up to polylogarithmic losses.

The proof is the tilted cluster test of `TiltedClusterNyquistExclusion` with the floor in place
of positivity. Its norms come from the derivative tails of the tilted divided kernel at weight
zero (`testθ_norm`), and `∫|f|² ≤ 2a ‖f‖₁ ‖f''‖₁` (`integral_norm_sq_le`).
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "shw" => OffLinePairData.sh
local notation "Mt" => tiltedPhiTailConst

theorem expTail_zero_zero (g : ℝ → ℂ) : expTail g 0 0 = ∫ u, ‖g u‖ := by
  unfold expTail
  congr 1; funext u
  simp [indicator]

namespace ClusterSetup

variable (C : ClusterSetup)

/-- The size `B_θ = 2^N ∫ ‖Φ_θ‖ e^{3N|u|/2}` of the tilted divided kernel. -/
def tiltedSize (θ : ℝ) : ℝ :=
  2 ^ windowCount C.t₀ * expTail (tiltedPhi θ) (3 / 2 * windowCount C.t₀) 0

theorem tiltedSize_nonneg (θ : ℝ) : 0 ≤ C.tiltedSize θ := by
  unfold tiltedSize; exact mul_nonneg (by positivity) (expTail_nonneg _ _ _)

/-- The `L¹` size of the tilted test and its second derivative:
`‖f‖₁ + ‖f''‖₁ ≤ 4 Kp Σ|c_k| (1 + cosh(s/2)) (t₀+3)² B_θ`. -/
theorem testθ_norm {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : XiDivisorSupport}
    (hρ₀ : ρ₀ ∈ C.nodes) (a : ℝ) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    (∫ u, ‖C.testθ θ a u‖) + (∫ u, ‖deriv (deriv (C.testθ θ a)) u‖) ≤
      4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
        ((C.t₀ + 3) ^ 2 * C.tiltedSize θ) := by
  obtain ⟨hK, -⟩ := C.Kθ_spec hθ0 hθ
  obtain ⟨k₁, k₂, hd1, hd2, sk₁, sk₂, t0, t1, t2⟩ := C.Kθ_calculus hθ0 hθ hρ₀
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  have e0 := t0 0 0 le_rfl
  have e1 := t1 0 0 le_rfl
  have e2 := t2 0 0 le_rfl
  rw [expTail_zero_zero, zero_add] at e0 e1 e2
  have nh : ∫ x, ‖C.Kθ θ x‖ ≤ C.tiltedSize θ := e0
  have nk₁ : ∫ x, ‖k₁ x‖ ≤ (1 + (C.t₀ + 2)) * C.tiltedSize θ := e1
  have nk₂ : ∫ x, ‖k₂ x‖ ≤ (1 + (C.t₀ + 2)) ^ 2 * C.tiltedSize θ := e2
  obtain ⟨-, hN⟩ := clusterTest_calculus hK hd1 hd2 sk₁.1 sk₂.1 (superExpDecay_integrable sk₁)
    (superExpDecay_integrable sk₂) hΓ nh nk₁ nk₂ C.Q C.κ (heightPolarShift C.t₀) (a - 1 / 4)
    hKp2 hKp
  have e : (1 + (C.t₀ + 2)) ^ 2 = (C.t₀ + 3) ^ 2 := by ring
  rw [e] at hN
  exact hN

/-- **The tilted cluster inequality under a floor.** If the bottom of the level-`a` Weil form is at
least `-η`, then `e^{2θ(t₀-3/4)} ≤ (16 + 4 S_Z) B_d² + 6 a η N₁₂²`, with `B_d = 6 Σ|c_k| · tailDecay`
and `N₁₂` the norm bound of `testθ_norm`. -/
theorem tilted_cluster_floor_inequality {ρ₀ : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes)
    {θ a η : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (ha : 0 ≤ a) (hη0 : 0 ≤ η)
    (hH : WeilFloorAtLevel zetaZeroConfig a η) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    Real.exp (θ * (C.t₀ - 3 / 4)) ^ 2 ≤
      (16 + 4 * zeroSumZ) * (6 * coeffMass C.Q * C.tailDecay θ a Kp) ^ 2 +
      6 * a * η * (4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
        ((C.t₀ + 3) ^ 2 * C.tiltedSize θ)) ^ 2 := by
  classical
  obtain ⟨hC2, hcomp, hts, hp1, hp2⟩ := C.testθ_properties hθ0 hθ hρ₀ a hKp2 hKp
  have hW0 := hH (C.testθ θ a) hC2 hts hp1 hp2
  have hN := C.testθ_norm hθ0 hθ hρ₀ a hKp2 hKp
  obtain ⟨-, hprod, -⟩ := C.K_spec
  have hKp0 : 0 ≤ Kp := by linarith
  set F : Finset zetaZeroConfig.carrier := C.nodes.image toCarrier with hF
  obtain ⟨Bd, hBd⟩ : ∃ x, x = 6 * coeffMass C.Q * C.tailDecay θ a Kp := ⟨_, rfl⟩
  have hcM := coeffMass_nonneg C.Q
  have hBd0 : 0 ≤ Bd := by rw [hBd]; exact mul_nonneg (by positivity) (C.tailDecay_nonneg θ a hKp0)
  have hS := zeroSumZ_nonneg
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
  rw [← hA]
  have hA0 : 0 < A := by rw [hA]; exact Real.exp_pos _
  obtain ⟨ηt, hηt⟩ : ∃ x, x = 6 * coeffMass C.Q * expTail (C.Kθ θ) (1 / 2) (a - 1 / 4 - shw) :=
    ⟨_, rfl⟩
  have hηt0 : 0 ≤ ηt := by rw [hηt]; exact mul_nonneg (by positivity) (expTail_nonneg _ _ _)
  have hηB : ηt ≤ Bd / 2 := by
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
    rw [hηt, hBd]
    have := mul_le_mul_of_nonneg_left e0 (by positivity : (0 : ℝ) ≤ 6 * coeffMass C.Q)
    nlinarith
  -- the `L²` norm of the test
  obtain ⟨N12, hN12⟩ : ∃ x, x = 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
      ((C.t₀ + 3) ^ 2 * C.tiltedSize θ) := ⟨_, rfl⟩
  rw [← hN12] at hN ⊢
  have hsupp : ∀ u, C.testθ θ a u ≠ 0 → |u| ≤ a := by
    have hsp0 : 0 ≤ heightPolarShift C.t₀ := by linarith [(heightPolarShift_mem C.ht₀).1]
    exact clusterTest_supp C.κ_pos.le hsp0 (C.test_supp_bound a)
  have hL2 : ∫ u, ‖C.testθ θ a u‖ ^ 2 ≤ 2 * a * N12 ^ 2 := by
    have h := integral_norm_sq_le ha hC2 hsupp
    obtain ⟨A1, hA1⟩ : ∃ x, x = ∫ u, ‖C.testθ θ a u‖ := ⟨_, rfl⟩
    obtain ⟨A2, hA2⟩ : ∃ x, x = ∫ u, ‖deriv (deriv (C.testθ θ a)) u‖ := ⟨_, rfl⟩
    rw [← hA1, ← hA2] at h hN
    have h1 : 0 ≤ A1 := by rw [hA1]; exact integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ A2 := by rw [hA2]; exact integral_nonneg fun _ => norm_nonneg _
    have h3 : A2 * A1 ≤ N12 ^ 2 := by
      have e : (A1 + A2) ^ 2 = A2 * A1 + (A1 ^ 2 + A1 * A2 + A2 ^ 2) := by ring
      have : A2 * A1 ≤ (A1 + A2) ^ 2 := by
        rw [e]
        exact le_add_of_nonneg_right
          (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg h1 h2)) (sq_nonneg _))
      exact this.trans (pow_le_pow_left₀ (add_nonneg h1 h2) hN 2)
    calc ∫ u, ‖C.testθ θ a u‖ ^ 2 ≤ 2 * a * A2 * A1 := h
      _ = 2 * a * (A2 * A1) := by ring
      _ ≤ 2 * a * N12 ^ 2 := mul_le_mul_of_nonneg_left h3 (by linarith)
  have hfl : η * ∫ u, ‖C.testθ θ a u‖ ^ 2 ≤ η * (2 * a * N12 ^ 2) :=
    mul_le_mul_of_nonneg_left hL2 hη0
  -- the node block, as in the Hodge case
  by_cases hηA : ηt ≤ A / 8
  · have hpair : ∀ ν ∈ C.nodes,
        (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re ≤
          (zetaZeroConfig.mult (toCarrier ν) : ℝ) * (-(3 / 8) * A ^ 2) := by
      intro ν hν
      obtain ⟨Y, hY, hYn⟩ := C.testθ_at_node hθ0 hθ a hν
      obtain ⟨Y', hY', hY'n⟩ := C.testθ_at_node hθ0 hθ a (C.reflect_mem_nodes hν)
      rw [← hηt] at hYn hY'n
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
        hmain hYn hY'n hηt0 hηAν
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
    have hBd2 : 0 ≤ Bd ^ 2 := sq_nonneg _
    have hSB : 0 ≤ zeroSumZ * Bd ^ 2 := mul_nonneg hS hBd2
    have hrest : 0 ≤ a * η * N12 ^ 2 := mul_nonneg (mul_nonneg ha hη0) (sq_nonneg _)
    rw [← hBd]
    linarith only [hsplit, hW0, hblock, hfl, hSB, hBd2, hrest]
  · push Not at hηA
    have hA8 : A ≤ 4 * Bd := by linarith only [hηA, hηB]
    have hsq : A ^ 2 ≤ (4 * Bd) ^ 2 := pow_le_pow_left₀ hA0.le hA8 2
    have hSB : 0 ≤ zeroSumZ * Bd ^ 2 := mul_nonneg hS (sq_nonneg _)
    have hrest : 0 ≤ a * η * N12 ^ 2 := mul_nonneg (mul_nonneg ha hη0) (sq_nonneg _)
    rw [← hBd]
    linarith only [hsq, hSB, hrest]

end ClusterSetup


/-- **Landau-sharp spectral separation, product form.** There are absolute constants `K₀, K₁`
such that, for every tilt `0 ≤ θ < π/4`, if the bottom of the level-`a` Weil form is at least
`-η` (`a ≥ 1`, `η ≥ 0`), then every nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > ½`, `t₀ ≥ 101` and
`6 + 3N/2 ≤ 2π cos(2θ) e^{2X}` (`X = a - 3/8`) satisfies

`e^{2θ(t₀ - 3/4)} ≤ K₀ (2^N (N+1) M (t₀+3)² e^{(6+3N/2)X} e^{-π cos(2θ) e^{2X}})²
  + K₁ a η ((N+1) M (t₀+3)² B_θ)²`,

with `M = interpBound(t₀, β₀ - ½, N)` and `B_θ = 2^N ∫‖Φ_θ‖ e^{3N|u|/2}`. Below the Landau horizon
of `hodgeIndex_tilted_cluster_horizon` the first term is negligible. There the zero forces
`μ(a) ≤ -e^{-2(π/4 - θ) t₀} / (poly(t₀, N, 1/δ₀) B_θ²)`. -/
theorem weilFloor_excludes_tilted_cluster :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {θ a η : ℝ}, 0 ≤ θ → 2 * θ < π / 2 → 1 ≤ a → 0 ≤ η →
      WeilFloorAtLevel zetaZeroConfig a η →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        6 + 3 / 2 * (windowCount ρ₀.im : ℝ) ≤
          2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) →
        Real.exp (2 * θ * (ρ₀.im - 3 / 4)) ≤
          K₀ * (2 ^ windowCount ρ₀.im * ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im)) *
            (ρ₀.im + 3) ^ 2 * (Real.exp ((6 + 3 / 2 * windowCount ρ₀.im) * (a - 3 / 8)) *
              Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))))) ^ 2 +
          K₁ * a * η * ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im) *
            (ρ₀.im + 3) ^ 2 * (2 ^ windowCount ρ₀.im *
              expTail (tiltedPhi θ) (3 / 2 * windowCount ρ₀.im) 0)) ^ 2 := by
  obtain ⟨Kp, hKp2, hKp⟩ := OffLinePairData.exists_plateau_constant
  have hS := zeroSumZ_nonneg
  have hM := tiltedPhiTailConst_nonneg
  have hKp0 : 0 ≤ Kp := by linarith
  refine ⟨(16 + 4 * zeroSumZ) * (96 * Kp * (Mt + 1)) ^ 2, 600 * Kp ^ 2,
    mul_pos (by positivity) (pow_pos (by positivity) 2), mul_pos (by norm_num)
      (pow_pos (by linarith) 2), ?_⟩
  intro θ a η hθ0 hθ ha hη0 hH ρ₀ hρ₀ hβ ht hlam
  obtain ⟨C, hCt, hCδ, ν₀, hν₀, -⟩ := exists_clusterSetup_node hρ₀ hβ ht
  have hraw := C.tilted_cluster_floor_inequality hν₀ hθ0 hθ (by linarith) hη0 hH hKp2 hKp
  have hne : C.nodes.Nonempty := ⟨ν₀, hν₀⟩
  set W := windowCount C.t₀ with hWdef
  have hWt : windowCount C.t₀ = windowCount ρ₀.im := by rw [hCt]
  rw [← hWt, ← hCt, ← hCδ]
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  have hMi1 : 1 ≤ Mi := by rw [hMidef]; exact C.one_le_interpBound
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  have hcM0 := coeffMass_nonneg C.Q
  have hsh : a - 1 / 4 - OffLinePairData.sh = a - 3 / 8 := by unfold OffLinePairData.sh; ring
  obtain ⟨τ, hτdef⟩ : ∃ x, x = expTail (tiltedPhi θ) (1 / 2 + 3 / 2 * W) (a - 3 / 8) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ x, x = Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
      Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hτE : τ ≤ 2 * (Mt + 1) * E := by
    rw [hτdef, hEdef]
    have h := expTail_tiltedPhi_le (c := 1 / 2 + 3 / 2 * W) (X := a - 3 / 8) hθ0 hθ
      (by positivity) (by rw [hWdef, hWt]; linarith)
    have e : (1 / 2 + 3 / 2 * (W : ℝ) + 11 / 2) = 6 + 3 / 2 * W := by ring
    rw [e] at h
    refine h.trans ?_
    have : 0 ≤ Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
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
  -- the Hodge part
  have hBd : 6 * coeffMass C.Q * C.tailDecay θ a Kp ≤
      96 * Kp * (Mt + 1) * (2 ^ W * ((W + 1) * Mi) * T * E) := by
    have s1 : C.tailDecay θ a Kp ≤ 8 * Kp * T * (2 ^ W * (2 * (Mt + 1) * E)) :=
      hdecay.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτE hpw0) (by positivity))
    have s2 : 6 * coeffMass C.Q * C.tailDecay θ a Kp ≤
        6 * ((W + 1) * Mi) * (8 * Kp * T * (2 ^ W * (2 * (Mt + 1) * E))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcM (by norm_num)) s1
        (C.tailDecay_nonneg θ a hKp0) (by positivity)
    refine s2.trans (le_of_eq ?_); ring
  have hBd0 : 0 ≤ 6 * coeffMass C.Q * C.tailDecay θ a Kp :=
    mul_nonneg (by positivity) (C.tailDecay_nonneg θ a hKp0)
  have hBd2 := pow_le_pow_left₀ hBd0 hBd 2
  -- the floor part
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
  have hN : 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
      ((C.t₀ + 3) ^ 2 * C.tiltedSize θ) ≤ 10 * Kp * ((W + 1) * Mi * T * C.tiltedSize θ) := by
    rw [← hTdef]
    have h1 : coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2)) ≤ ((W + 1) * Mi) * (5 / 2) :=
      mul_le_mul hcM hcosh hch0 (by positivity)
    calc 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
          (T * C.tiltedSize θ)
        ≤ 4 * Kp * (((W + 1) * Mi) * (5 / 2)) * (T * C.tiltedSize θ) := by gcongr
      _ = 10 * Kp * ((W + 1) * Mi * T * C.tiltedSize θ) := by ring
  have hN0 : 0 ≤ 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
      ((C.t₀ + 3) ^ 2 * C.tiltedSize θ) := by positivity
  have hN2 := pow_le_pow_left₀ hN0 hN 2
  have haη : 0 ≤ 6 * a * η := by have : 0 ≤ a := by linarith
                                 positivity
  have hraw2 := hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_left hBd2 (by positivity))
    (mul_le_mul_of_nonneg_left hN2 haη))
  have hexp : Real.exp (2 * θ * (C.t₀ - 3 / 4)) = Real.exp (θ * (C.t₀ - 3 / 4)) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [hexp]
  refine hraw2.trans (le_of_eq ?_)
  have hBθ : C.tiltedSize θ = 2 ^ W * expTail (tiltedPhi θ) (3 / 2 * W) 0 := rfl
  rw [hMidef, hTdef, hEdef, hBθ]
  ring


/-- **Landau-sharp spectral separation, logarithmic form.** With `K₀, K₁` as in
`weilFloor_excludes_tilted_cluster`: if the bottom of the level-`a` Weil form is at least `-η`
with `η > 0`, and a zero `β₀ + it₀` (`β₀ > ½`, `t₀ ≥ 101`) lies below the Landau horizon in the
sense `2K₀ P² ≤ e^{2θ(t₀ - 3/4)}`, where `P = 2^N (N+1) M (t₀+3)² e^{(6+3N/2)X - π cos(2θ) e^{2X}}`,
then

`log(1/η) ≤ 2(π/4 - θ) t₀ + π/2 + 3θ/2 + 2 L_N + 2 log(N+1) + 4 log(t₀+3) + 2 log B_θ + log(2K₁ a)`,

with `L_N` as in `hodgeIndex_tilted_cluster_horizon` and `B_θ = 2^N ∫‖Φ_θ‖ e^{3N|u|/2}`. For
every `ε = π/4 - θ > 0`, the eigenvalue forced by an off-line zero below the Landau horizon is
`≥ e^{-2ε t₀}` up to polylogarithmic factors and `B_θ²`. -/
theorem weilFloor_tilted_spectral_separation :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {θ a η : ℝ}, 0 ≤ θ → 2 * θ < π / 2 → 1 ≤ a → 0 < η →
      WeilFloorAtLevel zetaZeroConfig a η →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        6 + 3 / 2 * (windowCount ρ₀.im : ℝ) ≤
          2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) →
        2 * K₀ * (2 ^ windowCount ρ₀.im * ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im)) *
            (ρ₀.im + 3) ^ 2 * (Real.exp ((6 + 3 / 2 * windowCount ρ₀.im) * (a - 3 / 8)) *
              Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))))) ^ 2 ≤
          Real.exp (2 * θ * (ρ₀.im - 3 / 4)) →
        0 < expTail (tiltedPhi θ) (3 / 2 * windowCount ρ₀.im) 0 →
        Real.log (1 / η) ≤ 2 * (π / 4 - θ) * ρ₀.im + (π / 2 + 3 / 2 * θ) +
          2 * (Real.log 32 + windowCount ρ₀.im * Real.log 3 +
            windowCount ρ₀.im * Real.log (32 * (windowCount ρ₀.im + 1 : ℝ)) +
            2 * windowCount ρ₀.im * Real.log (16 * Real.exp 1 / (ρ₀.re - 1 / 2)) +
            (2 + windowCount ρ₀.im * Real.log 5 + 3 * (windowLogConst * Real.log ρ₀.im)) -
            Real.log (ρ₀.re - 1 / 2)) +
          2 * Real.log (windowCount ρ₀.im + 1) + 4 * Real.log (ρ₀.im + 3) +
          2 * Real.log (2 ^ windowCount ρ₀.im *
            expTail (tiltedPhi θ) (3 / 2 * windowCount ρ₀.im) 0) + Real.log (2 * K₁ * a) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, h⟩ := weilFloor_excludes_tilted_cluster
  refine ⟨K₀, K₁, hK₀, hK₁, fun {θ a η} hθ0 hθ ha hη hH {ρ₀} hρ₀ hβ ht hlam hland hB => ?_⟩
  have hmain := h hθ0 hθ ha hη.le hH hρ₀ hβ ht hlam
  set W := windowCount ρ₀.im
  set δ₀ := ρ₀.re - 1 / 2
  have hδ : 0 < δ₀ := by simp only [δ₀]; linarith
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound ρ₀.im δ₀ W := ⟨_, rfl⟩
  have hMi : 0 < Mi := by
    rw [hMidef]; unfold ClusterSetup.interpBound; have := Real.exp_pos 1; positivity
  rw [← hMidef] at hmain hland
  obtain ⟨PH, hPH⟩ : ∃ x, x = 2 ^ W * ((W + 1 : ℝ) * Mi) * (ρ₀.im + 3) ^ 2 *
      (Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))))) := ⟨_, rfl⟩
  obtain ⟨Bθ, hBθ⟩ : ∃ x, x = 2 ^ W * expTail (tiltedPhi θ) (3 / 2 * W) 0 := ⟨_, rfl⟩
  have hBθ0 : 0 < Bθ := by rw [hBθ]; positivity
  rw [← hPH] at hmain hland
  rw [← hBθ] at hmain ⊢
  obtain ⟨A2, hA2⟩ : ∃ x, x = Real.exp (2 * θ * (ρ₀.im - 3 / 4)) := ⟨_, rfl⟩
  rw [← hA2] at hmain hland
  have hA2pos : 0 < A2 := by rw [hA2]; exact Real.exp_pos _
  obtain ⟨PF, hPF⟩ : ∃ x, x = (W + 1 : ℝ) * Mi * (ρ₀.im + 3) ^ 2 * Bθ := ⟨_, rfl⟩
  rw [← hPF] at hmain
  have hPF0 : 0 < PF := by rw [hPF]; have : (0 : ℝ) < W + 1 := by positivity
                           have : (0 : ℝ) < ρ₀.im + 3 := by linarith
                           positivity
  have ha0 : 0 < a := by linarith
  -- `A²/2 ≤ K₁ a η PF²`
  have hkey : A2 ≤ 2 * K₁ * a * η * PF ^ 2 := by nlinarith
  have hηlb : A2 / (2 * K₁ * a * PF ^ 2) ≤ η := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hlog : Real.log (1 / η) ≤ Real.log (2 * K₁ * a * PF ^ 2) - Real.log A2 := by
    rw [← Real.log_div (by positivity) hA2pos.ne']
    apply Real.log_le_log (by positivity)
    rw [one_div, div_eq_mul_inv]
    have : A2 / (2 * K₁ * a * PF ^ 2) ≠ 0 := by positivity
    calc η⁻¹ ≤ (A2 / (2 * K₁ * a * PF ^ 2))⁻¹ := inv_anti₀ (by positivity) hηlb
      _ = 2 * K₁ * a * PF ^ 2 * A2⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hlA : Real.log A2 = 2 * θ * (ρ₀.im - 3 / 4) := by rw [hA2, Real.log_exp]
  have hW1 : (0 : ℝ) < W + 1 := by positivity
  have ht3 : (0 : ℝ) < ρ₀.im + 3 := by linarith
  have e1 : Real.log (2 * K₁ * a * PF ^ 2) = Real.log (2 * K₁ * a) + 2 * Real.log PF := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have hWM : (0 : ℝ) < (W + 1) * Mi := by positivity
  have hWMT : (0 : ℝ) < (W + 1) * Mi * (ρ₀.im + 3) ^ 2 := by positivity
  have e2 : Real.log PF = Real.log (W + 1) + Real.log Mi + 2 * Real.log (ρ₀.im + 3) +
      Real.log Bθ := by
    rw [hPF, Real.log_mul (x := (W + 1) * Mi * (ρ₀.im + 3) ^ 2) (y := Bθ) hWMT.ne' hBθ0.ne',
      Real.log_mul (x := (W + 1) * Mi) (y := (ρ₀.im + 3) ^ 2) hWM.ne' (by positivity),
      Real.log_mul hW1.ne' hMi.ne', Real.log_pow]
    push_cast; ring
  have hlPF : Real.log (2 * K₁ * a * PF ^ 2) =
      Real.log (2 * K₁ * a) + 2 * (Real.log (W + 1) + Real.log Mi + 2 * Real.log (ρ₀.im + 3) +
        Real.log Bθ) := by rw [e1, e2]
  have hLMi := log_interpBound ρ₀.im δ₀ hδ W
  rw [← hMidef] at hLMi
  rw [hlPF, hlA, hLMi] at hlog
  linarith

end

end RHTower
