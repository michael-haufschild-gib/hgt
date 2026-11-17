import GaloisForLFunctions.OrderSixMetaplecticTheory.TheWTypesOfTheCompositeTraceFoldOntoTheUTypes

/-!
# The composite Hecke trace in five blocks

For coprime primary primes `p, q` and `Θ` of multiplier `κ` on `Γ(3)` (`heckeTrace_eq_blocks`):

`Tr_mF_Θ = 2Θ^{hh}·Σ_xΘ^{ll}_x + 2(p/q)₃(Σ_uΘ^{hl}_u)(Σ_uΘ^{lh}_u) + 2B_{UL} + 2B_{LU} + B_{LL}`,

where the twisted blocks carry the characters `(3y/q)₃`, `(3y/p)₃`, `(3y/m)₃` of mean zero. The `W`-types fold onto the
`U`-types by translations of the residue fields; for `(W, L)` the fold also sends `y ↦ −y`, using
`t_y ≡ p⁻¹ + (9y)⁻¹` mod `q` (`Q_res_wlShift`) and `κ(W'_p)^{−2}κ(M_y) = (3c/q)₃` (`phase_WL`).
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPair

variable {R : PrimaryPair}

theorem sum_sum_add (f : R.P.Res → R.Q.Res → ℂ) (a : R.P.Res) (b : R.Q.Res) :
    ∑ x₁, ∑ x₂, f (x₁ + a) (x₂ + b) = ∑ x₁, ∑ x₂, f x₁ x₂ := by
  rw [Finset.sum_congr rfl fun x₁ _ => sum_add_right (fun x₂ => f (x₁ + a) x₂) b]
  exact sum_add_right (fun x₁ => ∑ x₂, f x₁ x₂) a

theorem sum_sum_mul_sum (s : ℂ) (A : R.Q.Res → ℂ) (B : R.P.Res → ℂ) :
    ∑ x₁, ∑ x₂, s * A x₂ * B x₁ = s * ((∑ u, A u) * ∑ u, B u) := by
  rw [Finset.sum_comm, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- The nine sums over the index of the cosets. -/
theorem sum_index (f : R.Index → ℂ) :
    ∑ ij, f ij =
      (∑ x₁, ∑ x₂, f (.inl x₁, .inl x₂)) + (∑ x₁, ∑ x₂, f (.inl x₁, .inr (.inl x₂))) +
        (∑ x₁, ∑ x₂, ∑ y₂, f (.inl x₁, .inr (.inr (x₂, y₂)))) + (∑ x₁, ∑ x₂, f (.inr (.inl x₁), .inl x₂)) +
        (∑ x₁, ∑ x₂, f (.inr (.inl x₁), .inr (.inl x₂))) +
        (∑ x₁, ∑ x₂, ∑ y₂, f (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) +
        (∑ x₁, ∑ y₁, ∑ x₂, f (.inr (.inr (x₁, y₁)), .inl x₂)) +
        (∑ x₁, ∑ y₁, ∑ x₂, f (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) +
        (∑ x₁, ∑ y₁, ∑ x₂, ∑ y₂, f (.inr (.inr (x₁, y₁)), .inr (.inr (x₂, y₂)))) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

section Fold

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hΘ

theorem ww_fold (w : HyperbolicSpace) :
    ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, R.ll Θ (R.mShift + R.xOf (.inr (.inl x₁), .inr (.inl x₂))) w * R.hh Θ w =
      R.hh Θ w * R.llSum Θ w := by
  have e : ∀ x₁ x₂, R.ll Θ (R.mShift + R.xOf (.inr (.inl x₁), .inr (.inl x₂))) w =
      R.ll Θ (R.crt (x₁ + (R.P.res R.mShift + R.P.res R.mDelta - R.P.res R.P.wDelta))
        (x₂ + (R.Q.res R.mShift + R.Q.res R.mDelta - R.Q.res R.Q.wDelta))) w := fun x₁ x₂ => by
    apply ll_congr Θ hΘ
    · simp [xOf]; ring
    · simp [xOf]; ring
  simp_rw [e]
  rw [sum_sum_add (fun x₁ x₂ => R.ll Θ (R.crt x₁ x₂) w * R.hh Θ w), llSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x₂ _ => mul_comm _ _

theorem uw_fold (w : HyperbolicSpace) :
    ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, (complexCharacter R.wQ ^ 2)⁻¹ * complexCharacter R.qHighUp *
        R.hl Θ (R.P.p * (R.qShift + R.xOf (.inl x₁, .inr (.inl x₂)))) w *
        R.lh Θ (1 + R.Q.p * R.xOf (.inl x₁, .inr (.inl x₂))) w =
      ringComplex (symbol R.P.p R.Q.p) * (R.hlSum Θ w * R.lhSum Θ w) := by
  have hq := R.P_q_mul_qInv
  have e1 : ∀ x₁ x₂, R.hl Θ (R.P.p * (R.qShift + R.xOf (.inl x₁, .inr (.inl x₂)))) w =
      R.hl Θ (R.Q.lift (R.Q.res R.P.p * x₂ +
        R.Q.res R.P.p * (R.Q.res R.qShift + R.Q.res R.qDelta - R.Q.res R.Q.wDelta))) w := fun x₁ x₂ => by
    apply hl_congr Θ hΘ
    simp [xOf]; ring
  have e2 : ∀ x₁ x₂, R.lh Θ (1 + R.Q.p * R.xOf (.inl x₁, .inr (.inl x₂))) w =
      R.lh Θ (R.P.lift (R.P.res R.Q.p * x₁ + 0)) w := fun x₁ x₂ => by
    apply lh_congr Θ hΘ
    simp [xOf]
    linear_combination (-1 : R.P.Res) * hq
  simp_rw [e1, e2, R.phase_UW]
  rw [sum_sum_mul_sum (ringComplex (symbol R.P.p R.Q.p))
    (fun x₂ => R.hl Θ (R.Q.lift (R.Q.res R.P.p * x₂ +
      R.Q.res R.P.p * (R.Q.res R.qShift + R.Q.res R.qDelta - R.Q.res R.Q.wDelta))) w)
    (fun x₁ => R.lh Θ (R.P.lift (R.P.res R.Q.p * x₁ + 0)) w),
    sum_mul_add (fun u => R.hl Θ (R.Q.lift u) w) _ _ R.Q_p_ne,
    sum_mul_add (fun u => R.lh Θ (R.P.lift u) w) _ _ R.P_q_ne, hlSum, lhSum]

theorem wu_fold (w : HyperbolicSpace) :
    ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, (complexCharacter R.wP ^ 2)⁻¹ * complexCharacter R.pHighUp *
        R.lh Θ (R.Q.p * (R.pShift + R.xOf (.inr (.inl x₁), .inl x₂))) w *
        R.hl Θ (1 + R.P.p * R.xOf (.inr (.inl x₁), .inl x₂)) w =
      ringComplex (symbol R.P.p R.Q.p) * (R.hlSum Θ w * R.lhSum Θ w) := by
  have hp := R.Q_p_mul_pInv
  have e1 : ∀ x₁ x₂, R.lh Θ (R.Q.p * (R.pShift + R.xOf (.inr (.inl x₁), .inl x₂))) w =
      R.lh Θ (R.P.lift (R.P.res R.Q.p * x₁ +
        R.P.res R.Q.p * (R.P.res R.pShift + R.P.res R.pDelta - R.P.res R.P.wDelta))) w := fun x₁ x₂ => by
    apply lh_congr Θ hΘ
    simp [xOf]; ring
  have e2 : ∀ x₁ x₂, R.hl Θ (1 + R.P.p * R.xOf (.inr (.inl x₁), .inl x₂)) w =
      R.hl Θ (R.Q.lift (R.Q.res R.P.p * x₂ + 0)) w := fun x₁ x₂ => by
    apply hl_congr Θ hΘ
    simp [xOf]
    linear_combination (-1 : R.Q.Res) * hp
  simp_rw [e1, e2, R.phase_WU]
  have hs : ∀ x₁ x₂, ringComplex (symbol R.P.p R.Q.p) *
      R.lh Θ (R.P.lift (R.P.res R.Q.p * x₁ +
        R.P.res R.Q.p * (R.P.res R.pShift + R.P.res R.pDelta - R.P.res R.P.wDelta))) w *
      R.hl Θ (R.Q.lift (R.Q.res R.P.p * x₂ + 0)) w =
      ringComplex (symbol R.P.p R.Q.p) * R.hl Θ (R.Q.lift (R.Q.res R.P.p * x₂ + 0)) w *
      R.lh Θ (R.P.lift (R.P.res R.Q.p * x₁ +
        R.P.res R.Q.p * (R.P.res R.pShift + R.P.res R.pDelta - R.P.res R.P.wDelta))) w := fun _ _ => by ring
  simp_rw [hs]
  rw [sum_sum_mul_sum (ringComplex (symbol R.P.p R.Q.p))
    (fun x₂ => R.hl Θ (R.Q.lift (R.Q.res R.P.p * x₂ + 0)) w)
    (fun x₁ => R.lh Θ (R.P.lift (R.P.res R.Q.p * x₁ +
      R.P.res R.Q.p * (R.P.res R.pShift + R.P.res R.pDelta - R.P.res R.P.wDelta))) w),
    sum_mul_add (fun u => R.hl Θ (R.Q.lift u) w) _ _ R.Q_p_ne,
    sum_mul_add (fun u => R.lh Θ (R.P.lift u) w) _ _ R.P_q_ne, hlSum, lhSum]

theorem wl_term (x₁ : R.P.Res) (x₂ : R.Q.Res) (y₂ : {y : R.Q.Res // y ≠ 0}) (w : HyperbolicSpace) :
    (complexCharacter R.wP ^ 2)⁻¹ * complexCharacter (R.wlMat (R.yWL y₂) (R.not_dvd_yWL y₂)) *
        R.ll Θ (R.wlShift (R.yWL y₂) + R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w *
        R.hl Θ (1 + R.P.p * R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w =
      ringComplex (symbol (3 * R.yUL (negY y₂)) R.Q.p) *
        R.hl Θ (R.P.p * R.crt (x₁ + (R.P.res (R.wlShift (R.yWL y₂)) + R.P.res R.pDelta - R.P.res R.P.wDelta))
          (x₂ + (9 * y₂.1)⁻¹) - R.Q.lowBeta (R.yUL (negY y₂))) w *
        R.ll Θ (R.crt (x₁ + (R.P.res (R.wlShift (R.yWL y₂)) + R.P.res R.pDelta - R.P.res R.P.wDelta))
          (x₂ + (9 * y₂.1)⁻¹)) w := by
  have hll : R.ll Θ (R.wlShift (R.yWL y₂) + R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w =
      R.ll Θ (R.crt (x₁ + (R.P.res (R.wlShift (R.yWL y₂)) + R.P.res R.pDelta - R.P.res R.P.wDelta))
        (x₂ + (9 * y₂.1)⁻¹)) w := by
    apply ll_congr Θ hΘ
    · simp [xOf]; ring
    · simp only [xOf, map_add, R.Q_res_crt, R.Q_res_wlShift]; ring
  have hhl : R.hl Θ (1 + R.P.p * R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w =
      R.hl Θ (R.P.p * R.crt (x₁ + (R.P.res (R.wlShift (R.yWL y₂)) + R.P.res R.pDelta - R.P.res R.P.wDelta))
        (x₂ + (9 * y₂.1)⁻¹) - R.Q.lowBeta (R.yUL (negY y₂))) w := by
    apply hl_congr Θ hΘ
    have hy := y₂.2
    have hp := R.Q_p_ne
    have h9 := R.Q.nine_ne_zero'
    simp only [xOf, map_add, map_sub, map_mul, map_one, R.Q_res_crt, R.Q_res_lowBeta_yUL]
    simp only [negY, pInv]
    field_simp
    ring
  rw [hll, hhl, R.phase_WL]
  ring

theorem lw_term (x₁ : R.P.Res) (y₁ : {y : R.P.Res // y ≠ 0}) (x₂ : R.Q.Res) (w : HyperbolicSpace) :
    (complexCharacter R.wQ ^ 2)⁻¹ * complexCharacter (R.lwMat (R.yLW y₁) (R.not_dvd_yLW y₁)) *
        R.ll Θ (R.lwShift (R.yLW y₁) + R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w *
        R.lh Θ (1 + R.Q.p * R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w =
      ringComplex (symbol (3 * R.yLU (negY y₁)) R.P.p) *
        R.lh Θ (R.Q.p * R.crt (x₁ + (9 * y₁.1)⁻¹)
          (x₂ + (R.Q.res (R.lwShift (R.yLW y₁)) + R.Q.res R.qDelta - R.Q.res R.Q.wDelta)) -
            R.P.lowBeta (R.yLU (negY y₁))) w *
        R.ll Θ (R.crt (x₁ + (9 * y₁.1)⁻¹)
          (x₂ + (R.Q.res (R.lwShift (R.yLW y₁)) + R.Q.res R.qDelta - R.Q.res R.Q.wDelta))) w := by
  have hll : R.ll Θ (R.lwShift (R.yLW y₁) + R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w =
      R.ll Θ (R.crt (x₁ + (9 * y₁.1)⁻¹)
        (x₂ + (R.Q.res (R.lwShift (R.yLW y₁)) + R.Q.res R.qDelta - R.Q.res R.Q.wDelta))) w := by
    apply ll_congr Θ hΘ
    · simp only [xOf, map_add, R.P_res_crt, R.P_res_lwShift]; ring
    · simp [xOf]; ring
  have hlh : R.lh Θ (1 + R.Q.p * R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w =
      R.lh Θ (R.Q.p * R.crt (x₁ + (9 * y₁.1)⁻¹)
        (x₂ + (R.Q.res (R.lwShift (R.yLW y₁)) + R.Q.res R.qDelta - R.Q.res R.Q.wDelta)) -
          R.P.lowBeta (R.yLU (negY y₁))) w := by
    apply lh_congr Θ hΘ
    have hy := y₁.2
    have hq := R.P_q_ne
    have h9 := R.P.nine_ne_zero'
    simp only [xOf, map_add, map_sub, map_mul, map_one, R.P_res_crt, R.P_res_lowBeta_yLU]
    simp only [negY, qInv]
    field_simp
    ring
  rw [hll, hlh, R.phase_LW]
  ring

theorem wl_fold (w : HyperbolicSpace) :
    ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
        (complexCharacter R.wP ^ 2)⁻¹ * complexCharacter (R.wlMat (R.yWL y₂) (R.not_dvd_yWL y₂)) *
        R.ll Θ (R.wlShift (R.yWL y₂) + R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w *
        R.hl Θ (1 + R.P.p * R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w = R.ulBlock Θ w := by
  set G : R.P.Res → R.Q.Res → {y : R.Q.Res // y ≠ 0} → ℂ := fun a b y =>
    ringComplex (symbol (3 * R.yUL y) R.Q.p) * R.hl Θ (R.P.p * R.crt a b - R.Q.lowBeta (R.yUL y)) w *
      R.ll Θ (R.crt a b) w with hG
  simp_rw [wl_term Θ hΘ]
  have hswap : ∀ F : R.P.Res → R.Q.Res → {y : R.Q.Res // y ≠ 0} → ℂ,
      ∑ x₁, ∑ x₂, ∑ y, F x₁ x₂ y = ∑ y, ∑ x₁, ∑ x₂, F x₁ x₂ y := fun F => by
    rw [Finset.sum_congr rfl fun x₁ _ => Finset.sum_comm, Finset.sum_comm]
  rw [hswap (fun x₁ x₂ y₂ => G (x₁ + (R.P.res (R.wlShift (R.yWL y₂)) + R.P.res R.pDelta - R.P.res R.P.wDelta))
    (x₂ + (9 * y₂.1)⁻¹) (negY y₂))]
  rw [Finset.sum_congr rfl fun y₂ _ => sum_sum_add (fun a b => G a b (negY y₂)) _ _]
  rw [show (∑ y₂, ∑ x₁, ∑ x₂, G x₁ x₂ (negY y₂)) = ∑ y, ∑ x₁, ∑ x₂, G x₁ x₂ y from
    sum_neg_units (fun y => ∑ x₁, ∑ x₂, G x₁ x₂ y), ← hswap G, ulBlock]

theorem lw_fold (w : HyperbolicSpace) :
    ∑ x₁ : R.P.Res, ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ x₂ : R.Q.Res,
        (complexCharacter R.wQ ^ 2)⁻¹ * complexCharacter (R.lwMat (R.yLW y₁) (R.not_dvd_yLW y₁)) *
        R.ll Θ (R.lwShift (R.yLW y₁) + R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w *
        R.lh Θ (1 + R.Q.p * R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w = R.luBlock Θ w := by
  set G : R.P.Res → {y : R.P.Res // y ≠ 0} → R.Q.Res → ℂ := fun a y b =>
    ringComplex (symbol (3 * R.yLU y) R.P.p) * R.lh Θ (R.Q.p * R.crt a b - R.P.lowBeta (R.yLU y)) w *
      R.ll Θ (R.crt a b) w with hG
  simp_rw [lw_term Θ hΘ]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun y₁ _ => sum_sum_add (fun a b => G a (negY y₁) b) _ _]
  rw [show (∑ y₁, ∑ x₁, ∑ x₂, G x₁ (negY y₁) x₂) = ∑ y, ∑ x₁, ∑ x₂, G x₁ y x₂ from
    sum_neg_units (fun y => ∑ x₁, ∑ x₂, G x₁ y x₂), Finset.sum_comm, luBlock]

/-- **The composite Hecke trace in five blocks.** -/
theorem heckeTrace_eq_blocks (w : HyperbolicSpace) :
    R.heckeTrace Θ w = 2 * (R.hh Θ w * R.llSum Θ w) +
      2 * ringComplex (symbol R.P.p R.Q.p) * (R.hlSum Θ w * R.lhSum Θ w) +
      2 * R.ulBlock Θ w + 2 * R.luBlock Θ w + R.llBlock Θ w := by
  rw [R.heckeTrace_eq_sum Θ hΘ w, sum_index]
  simp only [term_UU Θ hΘ, term_UW Θ hΘ, term_UL Θ hΘ, term_WU Θ hΘ, term_WW Θ hΘ, term_WL Θ hΘ,
    term_LU Θ hΘ, term_LW Θ hΘ, term_LL Θ hΘ]
  rw [uw_fold Θ hΘ, wu_fold Θ hΘ, ww_fold Θ hΘ, wl_fold Θ hΘ, lw_fold Θ hΘ]
  have hUU : ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res, R.hh Θ w * R.ll Θ (R.crt x₁ x₂) w = R.hh Θ w * R.llSum Θ w := by
    rw [llSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]
  rw [hUU, ulBlock, luBlock, llBlock]
  ring

end Fold

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
