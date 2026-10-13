import GaloisForLFunctions.RHTower.ZeroSideWeightedCertificate
import Zeta23.Tail
import Zeta23.Assembly

/-!
# The seam inequality for a weighted grid

For grid weights `w_k` with `|w_k| ≤ 1` put `G_w = diag(w) G diag(w)` (`wmat`).  The zero-side Gram matrix of `ζ`
splits as `G = A + E` (zeros in the window `I'` and the tail); the weighting acts on both pieces:

* `A_w` is the Gram matrix of the weighted block data, so the counting step holds for it
  (`weighted_rank_certificate`);
* `E_w = Σ_{tail} m_ρ (w·u_ρ)(w·u_ρ)ᵀ`, and since `‖w·u_ρ‖ ≤ ‖u_ρ‖` the trace-norm bound of the tail passes to it
  (`traceNorm_hat_wmat_Ez_le`: `‖Ê_w‖₁ ≤ θ₀/(aL)`).

Hence the seam inequality of the certificate holds for every such weighting (`seamA_weighted`):

`4 tr Ĝ_w − ‖Ĝ_w‖² − 2N(T,2T) − 3N(I′∖I) − B₀(4 + 2‖Ĝ_w‖_F + B₀) ≤ N₀*(T,2T)`,   `B₀ = θ₀/(aL)`.
-/

open Matrix Finset RHLinalg Zeta23 Zeta23.ZeroSide Zeta23.Tail Zeta23.Assembly
open scoped ComplexOrder

noncomputable section

namespace RHTower

section Weight

variable {d : Type*}

/-- **The weighting** `M ↦ diag(w) M diag(w)`. -/
def wmat (w : d → ℝ) (M : Matrix d d ℂ) : Matrix d d ℂ := fun k l => ((w k * w l : ℝ) : ℂ) * M k l

theorem wmat_add (w : d → ℝ) (M N : Matrix d d ℂ) : wmat w (M + N) = wmat w M + wmat w N := by
  ext k l; simp only [wmat, Matrix.add_apply]; ring

theorem wmat_smul (w : d → ℝ) (c : ℂ) (M : Matrix d d ℂ) : wmat w (c • M) = c • wmat w M := by
  ext k l; simp only [wmat, Matrix.smul_apply, smul_eq_mul]; ring

theorem wmat_isHermitian (w : d → ℝ) {M : Matrix d d ℂ} (hM : M.IsHermitian) :
    (wmat w M).IsHermitian := by
  ext k l
  have h : star (M l k) = M k l := by
    have := congrFun (congrFun hM k) l; rwa [conjTranspose_apply] at this
  rw [conjTranspose_apply]
  simp only [wmat, star_mul', ← h, RCLike.star_def, Complex.conj_ofReal]
  rw [mul_comm (w l) (w k)]

theorem wmat_vecMulVec (w : d → ℝ) (c : ℂ) (u : d → ℂ) :
    wmat w (c • vecMulVec u u) = c • vecMulVec (fun k => (w k : ℂ) * u k) (fun k => (w k : ℂ) * u k) := by
  ext k l; simp only [wmat, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]; push_cast; ring

theorem hasSum_wmat {ι : Type*} {f : ι → Matrix d d ℂ} {A : Matrix d d ℂ} (h : HasSum f A)
    (w : d → ℝ) : HasSum (fun i => wmat w (f i)) (wmat w A) := by
  refine Pi.hasSum.mpr fun k => Pi.hasSum.mpr fun l => ?_
  have hk := Pi.hasSum.mp (Pi.hasSum.mp h k) l
  simpa only [wmat] using hk.mul_left ((w k * w l : ℝ) : ℂ)

end Weight

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

/-- **The weighted tail**: `‖Ê_w‖₁ ≤ θ₀/(aL)`. -/
theorem traceNorm_hat_wmat_Ez_le (H : TailHyp Z P T A₀ C₁) (ha : 0 < P.a T) {w : Fin (P.d T) → ℝ}
    (hw : ∀ k, |w k| ≤ 1) (hE : (P.hat T (wmat w (Z.Ez P T))).IsHermitian) :
    traceNorm hE ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := by
  have hL := H.L_pos
  set κ : ℝ := (P.a T * P.L T ^ 2)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set u' : {ρ : Z.carrier // ρ ∉ H.sA} → Fin (P.d T) → ℂ :=
    fun x k => (w k : ℂ) * uvec P T (x : Z.carrier) k with hu'
  have hnorm : ∀ x, ∑ k, ‖u' x k‖ ^ 2 ≤ ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2 := by
    intro x
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [hu', norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have h1 : |w k| ^ 2 ≤ 1 := by have := abs_nonneg (w k); nlinarith [hw k]
    have h2 : 0 ≤ ‖uvec P T (x : Z.carrier) k‖ ^ 2 := sq_nonneg _
    nlinarith
  have hsum0 := H.summable_tail
  have hsummable : Summable (fun x : {ρ : Z.carrier // ρ ∉ H.sA} =>
      κ * (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖u' x k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (hsum0.mul_left κ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hnorm x) (by positivity)) hκ0
  have hE' : HasSum (fun x : {ρ : Z.carrier // ρ ∉ H.sA} =>
      (((κ * (Z.mult (x : Z.carrier) : ℝ) : ℝ) : ℂ)) • vecMulVec (u' x) (u' x))
      (P.hat T (wmat w (Z.Ez P T))) := by
    have h1 := hasSum_wmat H.hasSum_Ez w
    have h2 := h1.const_smul (((κ : ℝ) : ℂ))
    have e : P.hat T (wmat w (Z.Ez P T)) = ((κ : ℝ) : ℂ) • wmat w (Z.Ez P T) := by
      unfold Params.hat; rw [hκ]; push_cast; rfl
    rw [e]
    convert h2 using 1
    funext x
    rw [wmat_vecMulVec, smul_smul, Complex.ofReal_mul]
  have hS := hsummable.hasSum
  have hTN := traceNorm_le_of_hasSum_vecMulVec hE
    (fun x : {ρ : Z.carrier // ρ ∉ H.sA} => κ * (Z.mult (x : Z.carrier) : ℝ))
    (fun x => by positivity) u' hS hE'
  refine hTN.trans ?_
  have h1 : ∑' x : {ρ : Z.carrier // ρ ∉ H.sA}, κ * (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖u' x k‖ ^ 2
      ≤ κ * ∑' x : {ρ : Z.carrier // ρ ∉ H.sA},
          (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2 := by
    rw [← tsum_mul_left]
    refine hsummable.tsum_le_tsum (fun x => ?_) (hsum0.mul_left κ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hnorm x) (by positivity)) hκ0
  have h2 := mul_le_mul_of_nonneg_left H.tsum_tail_le hκ0
  have e : κ * (P.L T * theta0 A₀ H.K T) = theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := by
    rw [hκ]; unfold TailHyp.K; field_simp
  linarith

/-- **The weighted seam inequality.**  For grid weights `|w_k| ≤ 1`, with `Ĝ_w = (w_k w_l Ĝ_{kl})` and
`B₀ = θ₀/(aL)`: `4 tr Ĝ_w − ‖Ĝ_w‖² − 2N(T,2T) − 3N(I′∖I) − B₀(4 + 2‖Ĝ_w‖_F + B₀) ≤ N₀*(T,2T)`. -/
theorem seamA_weighted (hT : 0 ≤ T) (H : TailHyp Z P T A₀ C₁) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P) (ha : 0 < P.a T) {w : Fin (P.d T) → ℝ}
    (hw : ∀ k, |w k| ≤ 1) :
    4 * rtrace (P.hat T (wmat w (Z.Gz P T))) - frobSq (P.hat T (wmat w (Z.Gz P T)))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
      - theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T)
        * (4 + 2 * Real.sqrt (frobSq (P.hat T (wmat w (Z.Gz P T))))
          + theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T))
      ≤ Z.N0star T (2 * T) := by
  have hL := H.L_pos
  have hc : 0 < P.a T * P.L T ^ 2 := by positivity
  set D := blockData Z T P hconj with hD
  -- the window part is the weighted block Gram matrix
  have hAw : P.hat T (wmat w (Z.Az P T))
      = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • (weightBlock D w).blockA := by
    rw [ZeroSide.hat_eq]
    congr 1
    ext k l
    rw [weightBlock_blockA_apply, wmat, Az_eq_blockA Z T P hconj]
  have hcore0 := weighted_rank_certificate D (mkPairReps Z T _ (evalVec_reflect hconj)) hw hc
    (sum_normSq_v_le Z T P hconj hreal hPois)
  have hNc : (D.Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    rw [hD, blockData, ← NIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  have hs : ((D.s₁ + D.s₂ : ℕ) : ℝ) = ((Z.s1 T + Z.s2 T : ℕ) : ℝ) := by
    rw [hD, blockData, ← s1_eq_mk Z T _ (evalVec_reflect hconj),
      ← s2_eq_mk Z T _ (evalVec_reflect hconj)]
  rw [← hAw, hNc, hs] at hcore0
  -- the tail part
  have hGAE : P.hat T (wmat w (Z.Gz P T))
      = P.hat T (wmat w (Z.Az P T)) + P.hat T (wmat w (Z.Ez P T)) := by
    rw [← hat_add, ← wmat_add]; congr 2; simp [ZeroConfig.Ez]
  have hE : (P.hat T (wmat w (Z.Ez P T))).IsHermitian := by
    rw [ZeroSide.hat_eq]
    exact ZeroBlockData.isHermitian_real_smul (wmat_isHermitian w (H.Ez_isHermitian hconj)) _
  have hBle := traceNorm_hat_wmat_Ez_le H ha hw hE
  have hB0 := traceNorm_nonneg hE
  have hB₀ : 0 ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := hB0.trans hBle
  have hpert := four_tr_sub_frobSq_perturb hGAE hB₀ ((abs_rtrace_le_traceNorm hE).trans hBle)
    ((frobSq_le_traceNorm_sq hE).trans (pow_le_pow_left₀ hB0 hBle 2))
  have hcount' : ((Z.s1 T + Z.s2 T : ℕ) : ℝ) ≤ (Z.N0star T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_add_s2_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore0
  exact N0star_lower_explicit hcount' hcore0 hpert

end RHTower
