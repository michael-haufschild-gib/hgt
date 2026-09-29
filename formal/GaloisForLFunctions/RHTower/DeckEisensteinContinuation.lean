import GaloisForLFunctions.RHTower.DeckEisensteinSeries

/-!
# The continued deck Eisenstein series

Write `L = N + 1 ≥ 3` and `V_∞ = {v : ρ(T)v = v, ρ(−1)v = v}`.  Through the corpus expansion of
the continued `Γ(L)` Eisenstein series at the cusp `g∞`,
`E_∞(g z, s) = count₀(g) y^s + L^{-s}(y/L)^{1-s} φ_{∞,g∞}(s) + E^*_g(z, s)`,
the coordinate formula `Ẽ(z, s; v)_q = (2L)⁻¹ Σ_g v(q g⁻¹) E_∞(g z, s)` becomes, for `v ∈ V_∞`,

`Ẽ(z, s; v) = y^s v + y^{1-s} Φ̃(s) v + Ẽ^*(z, s; v)`,

with the scattering operator `(Φ̃(s) v)_q = (2L²)⁻¹ Σ_g φ_{∞,g∞}(s) v(q g⁻¹)` and the non-constant
part `Ẽ^*`.  The right side (`eisExt`) is holomorphic in `s` on the continuation domain `W \ {1}`,
which contains `Re s ≥ 1/2`, `s ≠ 1/2, 1`; it equals the series for `Re s > 1` and is
deck-equivariant for `Re s > 1/2`, `s ≠ 1`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

local instance gammaNormalDEC (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-- The cusp vectors `V_∞`: fixed by the translation `T` and by `−1`. -/
def IsCuspVec (v : DeckSpace N) : Prop :=
  deckRho N ModularGroup.T v = v ∧ deckRho N (-1) v = v

/-- **The scattering operator** `(Φ̃(s) v)_q = (2L²)⁻¹ Σ_g φ_{∞,g∞}(s) v(q g⁻¹)`. -/
def scatVec (s : ℂ) (v : DeckSpace N) : DeckSpace N :=
  WithLp.toLp 2 fun q => (2 * (N + 1 : ℂ) ^ 2)⁻¹ * ∑ g : Deck N,
    SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s * v (q * g⁻¹)

/-- The non-constant part `Ẽ^*(z, s; v)_q = (2L)⁻¹ Σ_g v(q g⁻¹) E^*_g(z, s)`. -/
def eisStarVec (s : ℂ) (v : DeckSpace N) (z : ℍ) : DeckSpace N :=
  WithLp.toLp 2 fun q => (2 * (N + 1 : ℂ))⁻¹ * ∑ g : Deck N,
    v (q * g⁻¹) * SelbergEisensteinStarCriticalLine.EstarExt (N + 1) (Quotient.out g) s z

/-- **The continued deck Eisenstein series** `y^s v + y^{1-s} Φ̃(s) v + Ẽ^*(z, s; v)`. -/
def eisExt (s : ℂ) (v : DeckSpace N) (z : ℍ) : DeckSpace N :=
  ((z.im : ℂ) ^ s) • v + ((z.im : ℂ) ^ (1 - s)) • scatVec s v + eisStarVec s v z

theorem scatVec_apply (s : ℂ) (v : DeckSpace N) (q : Deck N) :
    scatVec s v q = (2 * (N + 1 : ℂ) ^ 2)⁻¹ * ∑ g : Deck N,
      SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s * v (q * g⁻¹) := rfl

theorem eisStarVec_apply (s : ℂ) (v : DeckSpace N) (z : ℍ) (q : Deck N) :
    eisStarVec s v z q = (2 * (N + 1 : ℂ))⁻¹ * ∑ g : Deck N,
      v (q * g⁻¹) * SelbergEisensteinStarCriticalLine.EstarExt (N + 1) (Quotient.out g) s z := rfl

/-! ## The `y^s` multiplicity -/

open Classical in
theorem count0_eq (σ : SL(2, ℤ)) :
    (SelbergEisensteinCuspConstant.count0 (N + 1) σ : ℂ) =
      (if ((σ 1 0 : ℤ) : ZMod (N + 1)) = ((1 : SL(2, ℤ)) 1 0 : ℤ) ∧
          ((σ 1 1 : ℤ) : ZMod (N + 1)) = ((1 : SL(2, ℤ)) 1 1 : ℤ) then 1 else 0) +
      (if ((σ 1 0 : ℤ) : ZMod (N + 1)) = ((-1 : SL(2, ℤ)) 1 0 : ℤ) ∧
          ((σ 1 1 : ℤ) : ZMod (N + 1)) = ((-1 : SL(2, ℤ)) 1 1 : ℤ) then 1 else 0) := by
  unfold SelbergEisensteinCuspConstant.count0
  rw [Finset.card_filter, Finset.sum_pair (by norm_num : (1 : ℤ) ≠ -1)]
  push_cast
  have hmem : ∀ d : ℤ, IsCoprime (0 : ℤ) d → ((((0 : ℤ), d) ∈ SelbergEisensteinCusp.rowMul σ ''
      SelbergPoincareFourier.adm (N + 1)) ↔ ((0 : ZMod (N + 1)) = σ 1 0 ∧ ((d : ℤ) : ZMod (N + 1)) = σ 1 1)) := by
    intro d hd
    rw [SelbergEisensteinCuspCount.mem_image_congr]
    simp only [Int.cast_zero]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hd⟩⟩
  have h1 := hmem 1 isCoprime_one_right
  have h2 := hmem (-1) (isCoprime_one_right.neg_right)
  congr 1
  · by_cases h : (0 : ZMod (N + 1)) = σ 1 0 ∧ ((1 : ℤ) : ZMod (N + 1)) = σ 1 1
    · rw [if_pos (h1.2 h), if_pos]; simp only [Int.cast_one] at h
      simp [h.1.symm, h.2.symm]
    · rw [if_neg (fun h' => h (h1.1 h')), if_neg]
      intro h'
      apply h
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
        Matrix.one_apply_eq, Int.cast_zero, Int.cast_one] at h'
      simp [h'.1, h'.2]
  · by_cases h : (0 : ZMod (N + 1)) = σ 1 0 ∧ ((-1 : ℤ) : ZMod (N + 1)) = σ 1 1
    · rw [if_pos (h2.2 h), if_pos]; push_cast at h
      simp [h.1.symm, h.2.symm]
    · rw [if_neg (fun h' => h (h2.1 h')), if_neg]
      intro h'
      apply h
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq, neg_zero,
        Int.cast_zero, Int.cast_neg, Int.cast_one] at h'
      push_cast
      simp [h'.1, h'.2]

open Classical in
theorem sum_count0 {v : DeckSpace N} (hv : IsCuspVec v) (q : Deck N) :
    ∑ g : Deck N, v (q * g⁻¹) * (SelbergEisensteinCuspConstant.count0 (N + 1) (Quotient.out g) : ℂ) =
      2 * (N + 1 : ℂ) * v q := by
  have hinv : ∀ (n : ℤ) (g : Deck N),
      v (q * (QuotientGroup.mk (ModularGroup.T ^ n) * g)⁻¹) = v (q * g⁻¹) := by
    intro n g
    rw [mul_inv_rev, ← mul_assoc, ← QuotientGroup.mk_inv, ← deckRho_apply, ← zpow_neg,
      deckRho_T_zpow hv.1]
  simp_rw [count0_eq, mul_add, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib, sum_deck_bottomRow 1 (fun g => v (q * g⁻¹)) hinv,
    sum_deck_bottomRow (-1) (fun g => v (q * g⁻¹)) hinv]
  have hm : v (q * (QuotientGroup.mk (-1 : SL(2, ℤ)) : Deck N)⁻¹) = v q := by
    have h := congrArg (fun w : DeckSpace N => w q) hv.2
    simp only [deckRho_apply] at h
    rw [← QuotientGroup.mk_inv, inv_neg, inv_one]
    exact h
  rw [hm, QuotientGroup.mk_one, inv_one, mul_one]
  ring

/-! ## Agreement with the corpus continuation -/

theorem cexp_mul_div_cpow {s : ℂ} {y : ℝ} (hy : 0 < y) :
    Complex.exp (-s * (Real.log (N + 1 : ℕ) : ℂ)) * (((y / (N + 1 : ℕ) : ℝ)) : ℂ) ^ (1 - s) =
      (y : ℂ) ^ (1 - s) * (N + 1 : ℂ)⁻¹ := by
  have hL : (0 : ℝ) < (N + 1 : ℕ) := by exact_mod_cast Nat.succ_pos N
  have hdiv : ((y / (N + 1 : ℕ) : ℝ) : ℂ) = (y : ℂ) * (((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) := by
    push_cast; ring
  rw [hdiv, Complex.mul_cpow_ofReal_nonneg hy.le (inv_nonneg.2 hL.le)]
  have hne : ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (inv_pos.2 hL).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (inv_nonneg.2 hL.le), Real.log_inv]
  have e : Complex.exp (-s * (Real.log (N + 1 : ℕ) : ℂ)) *
      ((y : ℂ) ^ (1 - s) * Complex.exp (((-Real.log (N + 1 : ℕ) : ℝ) : ℂ) * (1 - s))) =
      (y : ℂ) ^ (1 - s) * Complex.exp (-(Real.log (N + 1 : ℕ) : ℂ)) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hL]
  push_cast
  ring

theorem EcuspExt_expand (σ : SL(2, ℤ)) (s : ℂ) (z : ℍ) :
    SelbergEisensteinCriticalLine.EcuspExt (N + 1) σ s z =
      (z.im : ℂ) ^ s * (SelbergEisensteinCuspConstant.count0 (N + 1) σ : ℂ) +
        (z.im : ℂ) ^ (1 - s) * (N + 1 : ℂ)⁻¹ * SelbergEisensteinCriticalLine.phiExt (N + 1) σ s +
        SelbergEisensteinStarCriticalLine.EstarExt (N + 1) σ s z := by
  rw [SelbergEisensteinCriticalLine.EcuspExt, cexp_mul_div_cpow z.im_pos]

/-- **Coordinates of the continued series**: for `v ∈ V_∞`,
`Ẽ(z, s; v)_q = (2L)⁻¹ Σ_g v(q g⁻¹) E_g(z, s)` with the corpus expansion `E_g` at the cusp `g∞`. -/
theorem eisExt_apply_eq_sum {v : DeckSpace N} (hv : IsCuspVec v) (s : ℂ) (z : ℍ) (q : Deck N) :
    eisExt s v z q = (2 * (N + 1 : ℂ))⁻¹ * ∑ g : Deck N,
      v (q * g⁻¹) * SelbergEisensteinCriticalLine.EcuspExt (N + 1) (Quotient.out g) s z := by
  have hL : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hsplit : ∀ g : Deck N, v (q * g⁻¹) *
      SelbergEisensteinCriticalLine.EcuspExt (N + 1) (Quotient.out g) s z =
      v (q * g⁻¹) * ((z.im : ℂ) ^ s * (SelbergEisensteinCuspConstant.count0 (N + 1) (Quotient.out g) : ℂ)) +
      v (q * g⁻¹) * ((z.im : ℂ) ^ (1 - s) * (N + 1 : ℂ)⁻¹ *
        SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s) +
      v (q * g⁻¹) * SelbergEisensteinStarCriticalLine.EstarExt (N + 1) (Quotient.out g) s z := by
    intro g
    rw [EcuspExt_expand]
    ring
  rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_add_distrib, Finset.sum_add_distrib]
  set K : ℂ := (2 * (N + 1 : ℂ))⁻¹ with hK
  rw [mul_add, mul_add]
  have h1 : K * ∑ g : Deck N, v (q * g⁻¹) * ((z.im : ℂ) ^ s *
      (SelbergEisensteinCuspConstant.count0 (N + 1) (Quotient.out g) : ℂ)) = (z.im : ℂ) ^ s * v q := by
    simp_rw [mul_left_comm (v _) ((z.im : ℂ) ^ s)]
    rw [← Finset.mul_sum, sum_count0 hv q, hK]
    field_simp
  have h2 : K * ∑ g : Deck N, v (q * g⁻¹) * ((z.im : ℂ) ^ (1 - s) *
      (N + 1 : ℂ)⁻¹ * SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s) =
      (z.im : ℂ) ^ (1 - s) * scatVec s v q := by
    rw [scatVec_apply, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hK]
    field_simp
  rw [h1, h2]
  simp only [eisExt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, eisStarVec_apply, hK]

/-- For `Re s > 1` the continued series is the deck Eisenstein series. -/
theorem eisVec_eq_eisExt (hN : 2 ≤ N) {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : IsCuspVec v) (z : ℍ) : eisVec s v z = eisExt s v z := by
  ext q
  rw [eisVec_apply_eq_sum hs hv.1, eisExt_apply_eq_sum hv]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  have h3 : 3 ≤ N + 1 := by omega
  rw [← SelbergEisensteinCriticalLine.Econt_smul_eq_EcuspExt (N + 1) _ h3 z (by linarith)
    (fun h => by rw [h] at hs; norm_num at hs)]
  rw [SelbergEisensteinContinuation.eisenstein_eq (N + 1) h3 hs]
  rfl

/-! ## Holomorphy in `s` -/

theorem differentiableAt_scatVec_apply (v : DeckSpace N) (q : Deck N) {s : ℂ}
    (hs : s ∈ SelbergEisensteinStarCriticalLine.Wset (N + 1)) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => scatVec s v q) s := by
  simp_rw [scatVec_apply]
  refine (differentiableAt_const _).mul (DifferentiableAt.fun_sum fun g _ => ?_)
  exact (SelbergEisensteinCriticalLine.differentiableAt_phiExt (N + 1) _ hs hs1).mul_const _

theorem differentiableAt_eisStarVec_apply (v : DeckSpace N) (z : ℍ) (q : Deck N) {s : ℂ}
    (hs : s ∈ SelbergEisensteinStarCriticalLine.Wset (N + 1)) :
    DifferentiableAt ℂ (fun s => eisStarVec s v z q) s := by
  simp_rw [eisStarVec_apply]
  refine (differentiableAt_const _).mul (DifferentiableAt.fun_sum fun g _ => ?_)
  exact (SelbergEisensteinStarCriticalLine.differentiableAt_EstarExt (N + 1) _ z hs).const_mul _

theorem differentiableAt_eisExt_apply (v : DeckSpace N) (z : ℍ) (q : Deck N) {s : ℂ}
    (hs : s ∈ SelbergEisensteinStarCriticalLine.Wset (N + 1)) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => eisExt s v z q) s := by
  have hy : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  simp only [eisExt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine (((differentiableAt_id.const_cpow (Or.inl hy)).mul_const _).add
    ((((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hy)).mul
      (differentiableAt_scatVec_apply v q hs hs1))).add (differentiableAt_eisStarVec_apply v z q hs)

theorem mem_Wset_of_half_lt {s : ℂ} (hs : 1 / 2 < s.re) :
    s ∈ SelbergEisensteinStarCriticalLine.Wset (N + 1) :=
  SelbergEisensteinStarCriticalLine.mem_Wset_of_half_le (N + 1) hs.le
    (fun h => by rw [h] at hs; norm_num at hs)

/-- **Equivariance of the continued series** on `Re s > 1/2`, `s ≠ 1`, by the identity theorem
from `Re s > 1`. -/
theorem eisExt_smul (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) (A : SL(2, ℤ)) (z : ℍ)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    eisExt s v (A • z) = deckRho N A (eisExt s v z) := by
  ext q
  set U := {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1}
  have hf : AnalyticOnNhd ℂ (fun s => eisExt s v (A • z) q) U :=
    DifferentiableOn.analyticOnNhd (fun s hs =>
      (differentiableAt_eisExt_apply v _ q (mem_Wset_of_half_lt hs.1) hs.2).differentiableWithinAt)
      SelbergEisensteinCuspExpansion.isOpen_punctured
  have hg : AnalyticOnNhd ℂ (fun s => deckRho N A (eisExt s v z) q) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) SelbergEisensteinCuspExpansion.isOpen_punctured
    rw [show (fun s => deckRho N A (eisExt s v z) q) = fun s => eisExt s v z (q * QuotientGroup.mk A) from
      funext fun s => deckRho_apply A _ q]
    exact (differentiableAt_eisExt_apply v z _ (mem_Wset_of_half_lt hs.1) hs.2).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hev : (fun s => eisExt s v (A • z) q) =ᶠ[𝓝 2] (fun s => deckRho N A (eisExt s v z) q) := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs'
    rw [← eisVec_eq_eisExt hN hs' hv, ← eisVec_eq_eisExt hN hs' hv, eisVec_smul hv.1]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg SelbergEisensteinCuspExpansion.isPreconnected_punctured
    h2 hev ⟨hs, hs1⟩

end

end GaloisForLFunctions.RHTower.DeckPointPair
