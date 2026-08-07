import GaloisForLFunctions.Bottcher.DyadicMonodromy
import GaloisForLFunctions.RHTower.SEMFittingCharge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Dyadic weld--Weyl multiplicity

One projective rank-two action forces an entire rung of the RH multiplicity ladder.  If two
invertible matrices on a `d`-dimensional complex space obey the Weyl relation

`U * V = ζ • (V * U)`

for a primitive `n`-th root `ζ`, determinants give `ζ ^ d = 1`, hence `n ∣ d`.  Taking `ζ` to be
the coherent depth-`k` Böttcher Prüfer multiplier forces `2 ^ k ∣ d`.

The final theorems apply this mechanism to the undoubled finite hole list of an actual
`SEMSplitData`.  They close the target end of the outlandish chain

`Böttcher Prüfer phase + rank-two weld -> internal Weyl action -> every RH rung -> RH`.

They do not construct the internal Weyl action.  In particular, tensoring with an auxiliary
clock--shift module is not an input to these declarations: the matrices act directly on
`Fin zs.length`, so their dimension is the actual SEM hole count.
-/

open Complex Matrix Set

namespace RHTower

noncomputable section

/-- The named Böttcher depth-`k` multiplier is a primitive `2^k`-th root of unity. -/
theorem dyadicWeylPhase_isPrimitiveRoot (k : ℕ) :
    IsPrimitiveRoot (Bottcher.dyadicRoot k) (2 ^ k) := by
  unfold Bottcher.dyadicRoot
  exact Complex.isPrimitiveRoot_exp (2 ^ k) (pow_ne_zero k (by norm_num))

/-- **Weyl determinant divisibility.**  An invertible finite-dimensional Weyl pair with primitive
commutator phase of order `n` forces its dimension to be divisible by `n`. -/
theorem dvd_card_of_invertible_weyl_pair {d n : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n)
    (U V : Matrix (Fin d) (Fin d) ℂ)
    (hU : U.det ≠ 0) (hV : V.det ≠ 0)
    (hweyl : U * V = ζ • (V * U)) :
    n ∣ d := by
  have hdet := congrArg Matrix.det hweyl
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at hdet
  have hprod : U.det * V.det ≠ 0 := mul_ne_zero hU hV
  have hscaled : (1 : ℂ) * (U.det * V.det) = ζ ^ d * (U.det * V.det) := by
    simpa [mul_comm] using hdet
  have hpow : ζ ^ d = 1 := by
    exact (mul_right_cancel₀ hprod hscaled).symm
  exact (hζ.pow_eq_one_iff_dvd d).mp hpow

/-- At Böttcher depth `k`, one invertible Weyl pair forces `2^k`-divisibility. -/
theorem pow_dvd_card_of_dyadic_weyl_pair {d k : ℕ}
    (U V : Matrix (Fin d) (Fin d) ℂ)
    (hU : U.det ≠ 0) (hV : V.det ≠ 0)
    (hweyl : U * V = Bottcher.dyadicRoot k • (V * U)) :
    2 ^ k ∣ d :=
  dvd_card_of_invertible_weyl_pair (dyadicWeylPhase_isPrimitiveRoot k) U V hU hV hweyl

/-- An **internal** dyadic Weyl model of an actual SEM split.  The matrices act on the split's
undoubled hole-index space `Fin zs.length`; there is no auxiliary tensor factor whose dimension
could manufacture the required divisibility. -/
structure SEMDyadicWeylModel (k : ℕ)
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (_h : SEMSplitData ρ r₀ R N zs u) : Type where
  U : Matrix (Fin zs.length) (Fin zs.length) ℂ
  V : Matrix (Fin zs.length) (Fin zs.length) ℂ
  det_U_ne_zero : U.det ≠ 0
  det_V_ne_zero : V.det ≠ 0
  weyl : U * V = Bottcher.dyadicRoot k • (V * U)

/-- An internal level-`k` Weyl model makes the actual SEM hole count divisible by `2^k`. -/
theorem SEMDyadicWeylModel.pow_dvd_holeCount {k : ℕ}
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    {h : SEMSplitData ρ r₀ R N zs u} (M : SEMDyadicWeylModel k h) :
    2 ^ k ∣ zs.length :=
  pow_dvd_card_of_dyadic_weyl_pair M.U M.V M.det_U_ne_zero M.det_V_ne_zero M.weyl

/-- **One internal Weyl level gives one RH rung.**  If every actual right-half SEM hole space carries
the source-selected depth-`k` Weyl pair, then every off-line `xi` order is divisible by `2^k`. -/
theorem rhLadder_of_semDyadicWeylModel (k : ℕ)
    (hmodel : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
        (h : SEMSplitData ρ r₀ R N zs u),
        Nonempty (SEMDyadicWeylModel k h)) :
    RHLadder k := by
  rw [rhLadder_iff_toNat_dvd]
  intro ρ hρ hzero
  have h0 : 0 < ρ.re := lt_trans (by norm_num) (mem_rightHalf.mp hρ)
  obtain ⟨r₀, R, N, zs, u, hsplit⟩ :=
    semSplitData_exists ρ h0 (xi_zero_re_lt_one hzero)
  obtain ⟨M⟩ := hmodel ρ hρ hzero r₀ R N zs u hsplit
  rw [semSplitData_count_eq hsplit]
  exact M.pow_dvd_holeCount

/-- **All internal dyadic Weyl levels imply RH.**  This is the exact target closure of the route;
the remaining open core is solely the source construction of the models. -/
theorem riemannHypothesis_of_all_semDyadicWeylModels
    (hmodel : ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
        (h : SEMSplitData ρ r₀ R N zs u),
        Nonempty (SEMDyadicWeylModel k h)) :
    RiemannHypothesis := by
  rw [rh_iff_forall_ladder]
  intro k
  exact rhLadder_of_semDyadicWeylModel k (hmodel k)

/-- Cofinal internal Weyl levels already imply RH: level coherence need only supply models at
unboundedly many dyadic depths. -/
theorem riemannHypothesis_of_cofinal_semDyadicWeylModels
    (hmodel : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ)
          (h : SEMSplitData ρ r₀ R N zs u),
          Nonempty (SEMDyadicWeylModel k h)) :
    RiemannHypothesis := by
  apply rh_of_rhLadder_cofinal
  intro K
  obtain ⟨k, hKk, hk⟩ := hmodel K
  exact ⟨k, hKk, rhLadder_of_semDyadicWeylModel k hk⟩

end

end RHTower
