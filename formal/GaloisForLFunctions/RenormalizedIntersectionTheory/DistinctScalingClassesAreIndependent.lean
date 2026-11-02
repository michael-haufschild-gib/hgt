import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWeilKernelHasNoFiniteRankRealization
import GaloisForLFunctions.HTGeometry.WeightedDirichletZeroCount

/-!
# Distinct scaling classes are independent in Weil's pairing

`TheWeilKernelHasNoFiniteRankRealization` rules out one finite-dimensional height space for all
scaling classes. This module makes the rank requirement exact on the integer slopes.

* **The critical part is positive definite on integer slopes** (`hermQuad_gram_onLine_natSlope_pos`,
  unconditional): for distinct positive integers `n_1, …, n_k`, the Gram matrix of the on-line part
  `K_on = Σ_γ m_γ |B̂(γ)|² u^{−iγ}` of Weil's kernel is positive definite. Its form is
  `Σ_γ m_γ |B̂(γ)|² |Σ_b c_b n_b^{−iγ}|²`; if it vanished, the nonzero Dirichlet polynomial
  `Σ_b c̄_b n_b^{iτ}` would vanish at every seen critical ordinate. Those number at least
  `c₀ T log T − T/π − 1` in `(T, 2T]` (`exists_many_critical_ordinates_dyadic`, minus the lattice
  `πℤ` where the cubic spline is blind), while a nonzero Dirichlet polynomial has at most `K(1 + 2T)`
  real zeros in `[0, 2T]` (`exists_zero_count_linear`).
* **Under RH, Weil's Gram on the slopes `1, …, N` has `N` positive squares**
  (`hermPosIndex_gram_zetaKernel_natSlope_of_riemannHypothesis`): with no right zeros, `K_ζ = K_on`.
* **The tower rank law** (`card_le_of_gram_factor_of_riemannHypothesis`): any factorization of that
  Gram matrix through `r` coordinates, `Aᴴ diag(d) A` with `A : r × N` — the intersection matrix of the
  slopes in an `r`-dimensional height space — has `r ≥ N`.

So a tower carrying the integer scaling classes needs rank at least `N` at the level where the
slopes `1, …, N` live; the Gram matrix itself shows that `N` is attained.
-/

open Complex Matrix Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros cx)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The integer scaling class `n + 1 ∈ ℚ_{>0}`. -/
def natSlope (n : ℕ) : HeckeLattice := ⟨((n + 1 : ℕ) : ℚ), by positivity⟩

theorem scale_natSlope (n : ℕ) : scale heckeLogScale (natSlope n) = Real.log ((n + 1 : ℕ) : ℝ) := by
  rw [scale_heckeLogScale]
  simp [natSlope]

/-- A positive-definite form has full positive index. -/
theorem hermPosIndex_eq_card_of_pos {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ}
    (h : ∀ c : ι → ℂ, c ≠ 0 → 0 < hermQuad M c) : hermPosIndex M = Fintype.card ι := by
  apply le_antisymm
  · apply csSup_le (posIndexSet_nonempty M)
    rintro r ⟨W, rfl, -⟩
    have h := Submodule.finrank_le W
    rwa [Module.finrank_fintype_fun_eq_card] at h
  · have hmem : Fintype.card ι ∈ hermPosIndexSet M :=
      ⟨⊤, by simp, fun c _ hc => h c hc⟩
    exact le_csSup (posIndexSet_bddAbove M) hmem

/-- A form that factors through `r` coordinates has at most `r` positive squares. -/
theorem hermPosIndex_le_of_factor {ι : Type*} [Fintype ι] {r : ℕ} {M : Matrix ι ι ℂ}
    (A : Matrix (Fin r) ι ℂ) (d : Fin r → ℂ) (hM : M = Aᴴ * (diagonal d * A)) :
    hermPosIndex M ≤ r := by
  classical
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex M
  have hzero : ∀ c : ι → ℂ, A *ᵥ c = 0 → hermQuad M c = 0 := by
    intro c hc
    rw [hM, hermQuad, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp [hc]
  have hinj : Function.Injective (A.mulVecLin.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    by_contra hw0
    have hne : (w : ι → ℂ) ≠ 0 := fun h => hw0 (Subtype.ext h)
    have h1 := hpos w w.2 hne
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, Matrix.mulVecLin_apply] at hw
    rw [hzero _ hw] at h1
    exact lt_irrefl _ h1
  rw [← hW]
  calc Module.finrank ℂ W ≤ Module.finrank ℂ (Fin r → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = r := by simp

/-- An off-lattice critical ordinate is a zero seen by the cubic spline. -/
theorem mem_criticalSeen_of_Xi {τ : ℝ} (hτ0 : τ ≠ 0) (hlat : ∀ n : ℤ, τ ≠ n * π)
    (hXi : RHTower.Xi τ = 0) : ((1 / 2 : ℂ) + (τ : ℂ) * I) ∈ criticalSeen := by
  refine ⟨?_, by simp, ?_⟩
  · rw [RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip]
    refine ⟨?_, by norm_num, by norm_num⟩
    rw [RHTower.xiHalfLine_real, hXi, ofReal_zero]
  · have him : ((1 / 2 : ℂ) + (τ : ℂ) * I).im = τ := by simp
    rw [him]
    exact paperFT_cubicSpline_ne_zero_of_real hτ0 hlat

/-- The Dirichlet readout of a finitely supported coefficient family. -/
theorem dirichletReadout_slopes {ι : Type*} [Fintype ι] {s : ι → ℕ} (hs : Function.Injective s)
    (c : ι → ℂ) (τ : ℝ) :
    dirichletReadout (fun n => ∑ b, if s b + 1 = n then conj (c b) else 0) τ =
      ∑ b, conj (c b) * cexp (((Real.log ((s b + 1 : ℕ) : ℝ) * τ : ℝ) : ℂ) * I) := by
  classical
  set C : ℕ → ℂ := fun n => ∑ b, if s b + 1 = n then conj (c b) else 0
  have hinj : Function.Injective fun b => s b + 1 := fun a b h => hs (by simpa using h)
  have hC : ∀ b, C (s b + 1) = conj (c b) := fun b => by
    simp only [C, Nat.add_right_cancel_iff, hs.eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have hsupp : ∀ n ∉ Finset.univ.image (fun b => s b + 1),
      LSeries.term C (-(I * (τ : ℂ))) n = 0 := by
    intro n hn
    have hCn : C n = 0 := by
      refine Finset.sum_eq_zero fun b _ => if_neg fun h => hn ?_
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, h⟩
    by_cases h0 : n = 0
    · simp [h0]
    · rw [LSeries.term_of_ne_zero h0, hCn, zero_div]
  unfold dirichletReadout LSeries
  rw [tsum_eq_sum hsupp, Finset.sum_image fun a _ b _ h => hinj h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero _), hC, cpow_neg, div_inv_eq_mul,
    natCast_cpow_I_mul _ (Nat.succ_ne_zero _), GaloisForLFunctions.expChar]

/-- **The critical part of Weil's kernel is positive definite on distinct integer slopes.** -/
theorem hermQuad_gram_onLine_natSlope_pos {ι : Type*} [Fintype ι] {s : ι → ℕ}
    (hs : Function.Injective s) {c : ι → ℂ} (hc : c ≠ 0) :
    0 < hermQuad (gram (orbitKernel zetaOnLine cubicSpline) fun b => natSlope (s b)) c := by
  classical
  obtain ⟨e⟩ := exists_enum_onLine
  set x : ι → HeckeLattice := fun b => natSlope (s b)
  rw [orbitKernel_onLine_eq_bohrSum e,
    hermQuad_gram_bohrSum (isUnitaryChar_onLineChar e) (summable_onLineWeight e)]
  set F : ℕ → ℝ := fun j => onLineWeight e j * normSq (charEval (onLineChar e j) x c)
  have hw0 : ∀ j, 0 ≤ onLineWeight e j := fun j => by
    simp only [onLineWeight, Wsummand_onLine (e j).2, ofReal_re]
    positivity
  have hF0 : ∀ j, 0 ≤ F j := fun j => mul_nonneg (hw0 j) (normSq_nonneg _)
  have hFs : Summable F := by
    refine (summable_onLineWeight e).mul_right ((∑ b, ‖c b‖) ^ 2) |>.of_nonneg_of_le hF0 ?_
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (hw0 j)
    rw [normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_charEval_le (isUnitaryChar_onLineChar e) x c j) 2
  rcases (tsum_nonneg hF0).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  -- every seen critical ordinate is a zero of the Dirichlet polynomial `Σ_b c̄_b n_b^{iτ}`
  set C : ℕ → ℂ := fun n => ∑ b, if s b + 1 = n then conj (c b) else 0
  have hvan : ∀ τ : ℝ, ((1 / 2 : ℂ) + (τ : ℂ) * I) ∈ criticalSeen → dirichletReadout C τ = 0 := by
    intro τ hρ
    set ρ : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * I
    have hρon := criticalSeen_subset hρ
    set j := e.symm ⟨ρ, hρon⟩
    have hej : (e j : ℂ) = ρ := by simp [j]
    have hwpos : 0 < onLineWeight e j := by
      simp only [onLineWeight, Wsummand_onLine (e j).2, ofReal_re, hej]
      have hm : (1 : ℝ) ≤ zetaOnLine.mult ρ := by exact_mod_cast zetaOnLine.one_le_mult ρ hρon
      have hF : 0 < ‖paperFT (cx cubicSpline) (ρ.im : ℂ)‖ := norm_pos_iff.mpr hρ.2.2
      positivity
    have hFj : F j = 0 := le_antisymm
      ((hFs.le_tsum j fun k _ => hF0 k).trans heq.ge) (hF0 j)
    have hev : charEval (onLineChar e j) x c = 0 := by
      have := (mul_eq_zero.mp hFj).resolve_left hwpos.ne'
      exact normSq_eq_zero.mp this
    have him : (e j : ℂ).im = τ := by rw [hej]; simp [ρ]
    rw [dirichletReadout_slopes hs c τ]
    have hconj := congrArg conj hev
    rw [map_zero, charEval_apply, map_sum] at hconj
    rw [← hconj]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [onLineChar, logChar_apply, x, scale_natSlope, him, map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  -- the polynomial is nonzero
  obtain ⟨b₀, hb₀⟩ : ∃ b, c b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  have hCne : ∃ n, 0 < n ∧ C n ≠ 0 := by
    refine ⟨s b₀ + 1, Nat.succ_pos _, ?_⟩
    simp only [C, Nat.add_right_cancel_iff, hs.eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    exact (map_ne_zero _).mpr hb₀
  have hCsum : WeightedAbsSummable C 1 := by
    apply summable_of_ne_finset_zero (s := Finset.univ.image fun b => s b + 1)
    intro n hn
    have hCn : C n = 0 := by
      refine Finset.sum_eq_zero fun b _ => if_neg fun h => hn ?_
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, h⟩
    simp [hCn]
  obtain ⟨K, hK0, hcount⟩ := exists_zero_count_linear hCsum one_pos hCne
  -- count: `c₀ T log T − T/π − 1 ≤ K (1 + 2T)` fails for large `T`
  obtain ⟨c₀, hc₀, T₀, hT₀, hmany⟩ := RHTower.exists_many_critical_ordinates_dyadic
  set T : ℝ := max T₀ (Real.exp ((1 / π + 1 + 3 * K) / c₀ + 1))
  have hTT₀ : T₀ ≤ T := le_max_left _ _
  have hTe : Real.exp ((1 / π + 1 + 3 * K) / c₀ + 1) ≤ T := le_max_right _ _
  have hT1 : 1 ≤ T := hT₀.trans hTT₀
  have hT0 : 0 < T := by linarith
  have hlog : (1 / π + 1 + 3 * K) / c₀ + 1 ≤ Real.log T := by
    rw [← Real.log_exp ((1 / π + 1 + 3 * K) / c₀ + 1)]
    exact Real.log_le_log (Real.exp_pos _) hTe
  have hclog : 1 / π + 1 + 3 * K < c₀ * Real.log T := by
    have : (1 / π + 1 + 3 * K) / c₀ < Real.log T := by linarith
    rwa [div_lt_iff₀ hc₀, mul_comm] at this
  obtain ⟨τS, hτS, hcard⟩ := hmany T hTT₀
  have hL := card_filter_lattice_le hT0.le τS fun τ hτ => ⟨(hτS τ hτ).1, (hτS τ hτ).2.1⟩
  set S := τS.filter fun τ => ¬ ∃ n : ℤ, τ = n * π
  have hSzero : ∀ τ ∈ S, 0 ≤ τ ∧ τ ≤ 2 * T ∧ dirichletReadout C τ = 0 := by
    intro τ hτ
    obtain ⟨hτ, hlat⟩ := mem_filter.mp hτ
    obtain ⟨h1, h2, hXi⟩ := hτS τ hτ
    have hτ0 : τ ≠ 0 := by linarith
    refine ⟨by linarith, h2, hvan τ (mem_criticalSeen_of_Xi hτ0 (fun n hn => hlat ⟨n, hn⟩) hXi)⟩
  have hSle := hcount (2 * T) (by linarith) S hSzero
  have hsplit := card_filter_add_card_filter_not (s := τS) (p := fun τ => ∃ n : ℤ, τ = n * π)
  have hsum : (τS.card : ℝ) = (τS.filter fun τ => ∃ n : ℤ, τ = n * π).card + S.card := by
    exact_mod_cast hsplit.symm
  have hbig : T / π + 1 + K * (1 + 2 * T) < c₀ * (T * Real.log T) := by
    have h1 : T * (1 / π + 1 + 3 * K) < T * (c₀ * Real.log T) :=
      mul_lt_mul_of_pos_left hclog hT0
    have h2 : T / π = T * (1 / π) := by ring
    nlinarith
  linarith

/-- **Under RH Weil's kernel is its critical part.** -/
theorem zetaKernel_eq_onLine_of_riemannHypothesis (hRH : RiemannHypothesis) (u : HeckeLattice) :
    zetaKernel u = orbitKernel zetaOnLine cubicSpline u := by
  have h0 := riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH
  rw [negIndex_zetaKernel, Set.encard_eq_zero] at h0
  have hR : (rightZeros zetaZeroConfig).Finite := h0 ▸ Set.finite_empty
  rw [zetaKernel, orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests hR u]
  have hempty : hR.toFinset = ∅ := by simp [h0]
  rw [hempty, Finset.sum_empty, add_zero]

/-- **Under RH, Weil's Gram matrix on distinct integer slopes has full positive index.** -/
theorem hermPosIndex_gram_zetaKernel_natSlope_of_riemannHypothesis (hRH : RiemannHypothesis)
    {ι : Type*} [Fintype ι] {s : ι → ℕ} (hs : Function.Injective s) :
    hermPosIndex (gram zetaKernel fun b => natSlope (s b)) = Fintype.card ι := by
  have hk : zetaKernel = orbitKernel zetaOnLine cubicSpline :=
    funext (zetaKernel_eq_onLine_of_riemannHypothesis hRH)
  rw [hk]
  exact hermPosIndex_eq_card_of_pos fun c hc => hermQuad_gram_onLine_natSlope_pos hs hc

/-- **The tower rank law.** Under RH, a factorization of Weil's Gram matrix on distinct integer
slopes through `r` coordinates needs `r` at least the number of slopes. -/
theorem card_le_of_gram_factor_of_riemannHypothesis (hRH : RiemannHypothesis)
    {ι : Type*} [Fintype ι] {s : ι → ℕ} (hs : Function.Injective s) {r : ℕ}
    (A : Matrix (Fin r) ι ℂ) (d : Fin r → ℂ)
    (hM : gram zetaKernel (fun b => natSlope (s b)) = Aᴴ * (diagonal d * A)) :
    Fintype.card ι ≤ r := by
  rw [← hermPosIndex_gram_zetaKernel_natSlope_of_riemannHypothesis hRH hs]
  exact hermPosIndex_le_of_factor A d hM

/-- The slopes `1, …, N` need rank `N`. -/
theorem le_of_gram_factor_slopes_of_riemannHypothesis (hRH : RiemannHypothesis) {N r : ℕ}
    (A : Matrix (Fin r) (Fin N) ℂ) (d : Fin r → ℂ)
    (hM : gram zetaKernel (fun b : Fin N => natSlope b) = Aᴴ * (diagonal d * A)) : N ≤ r := by
  have h := card_le_of_gram_factor_of_riemannHypothesis hRH (s := fun b : Fin N => (b : ℕ))
    Fin.val_injective A d hM
  simpa using h

end GaloisForLFunctions.RenormalizedIntersectionTheory
