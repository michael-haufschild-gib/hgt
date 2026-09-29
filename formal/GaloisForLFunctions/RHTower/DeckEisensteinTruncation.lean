import GaloisForLFunctions.RHTower.DeckEisensteinContinuation
import GaloisForLFunctions.RHTower.EisensteinUnfoldedRowSum
import GaloisForLFunctions.RHTower.EisensteinHyperbolicChart

/-!
# Truncation of the deck Eisenstein series

The bilinear deck pairing is `⟨X, Y⟩_β = Σ_q X_q Y_q`; it is invariant under the regular deck action.
The scattering operator preserves `V_∞`: its kernel `g ↦ φ_{∞,g∞}(s)` depends only on the
entry `g₁₀` modulo `L`.

For `Re s > 1`, `v ∈ V_T` and `w ∈ V_∞`, the horocycle average of the deck Eisenstein series is its
constant term: `∫_0^1 ⟨v, Ẽ(x + iy, s; w)⟩_β dx = ⟨v, y^s w + y^{1-s} Φ̃(s) w⟩_β` (corpus
`integral_poincare_cusp_phi` at each cusp, after `x ↦ x + 1` periodicity).

On `𝒟` and for `Y ≥ 1`, only the rows `±(0, 1)` lift a point above height `Y`, so the truncation
`Λ^Y Ẽ = Ẽ − [y > Y](y^s v + y^{1-s} Φ̃(s) v)` is the truncated row sum
`½ Σ_{(c,d)} [Im M_{c,d}z ≤ Y] Im(M_{c,d} z)^s ρ(M_{c,d})⁻¹ v − [y > Y] y^{1-s} Φ̃(s) v`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

local instance gammaNormalDET (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-! ## The bilinear deck pairing -/

/-- The bilinear pairing `⟨X, Y⟩_β = Σ_q X_q Y_q`. -/
def bil (X Y : DeckSpace N) : ℂ := ∑ q : Deck N, X q * Y q

theorem bil_comm (X Y : DeckSpace N) : bil X Y = bil Y X := by
  unfold bil; simp_rw [mul_comm]

theorem bil_add_left (X X' Y : DeckSpace N) : bil (X + X') Y = bil X Y + bil X' Y := by
  unfold bil; simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem bil_add_right (X Y Y' : DeckSpace N) : bil X (Y + Y') = bil X Y + bil X Y' := by
  unfold bil; simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]

theorem bil_sub_right (X Y Y' : DeckSpace N) : bil X (Y - Y') = bil X Y - bil X Y' := by
  unfold bil; simp only [PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem bil_sub_left (X X' Y : DeckSpace N) : bil (X - X') Y = bil X Y - bil X' Y := by
  unfold bil; simp only [PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem bil_smul_left (c : ℂ) (X Y : DeckSpace N) : bil (c • X) Y = c * bil X Y := by
  unfold bil; simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem bil_smul_right (c : ℂ) (X Y : DeckSpace N) : bil X (c • Y) = c * bil X Y := by
  unfold bil; simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem bil_zero_right (X : DeckSpace N) : bil X 0 = 0 := by
  unfold bil; simp

theorem bil_zero_left (Y : DeckSpace N) : bil 0 Y = 0 := by
  unfold bil; simp

/-- The coordinatewise conjugate. -/
def deckConjVec (X : DeckSpace N) : DeckSpace N := WithLp.toLp 2 fun q => conj (X q)

theorem bil_eq_inner (X Y : DeckSpace N) : bil X Y = ⟪deckConjVec X, Y⟫_ℂ := by
  rw [bil, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [deckConjVec, RCLike.inner_apply, mul_comm]

theorem norm_deckConjVec (X : DeckSpace N) : ‖deckConjVec X‖ = ‖X‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [deckConjVec]

theorem norm_bil_le (X Y : DeckSpace N) : ‖bil X Y‖ ≤ ‖X‖ * ‖Y‖ := by
  rw [bil_eq_inner, ← norm_deckConjVec X]
  exact norm_inner_le_norm _ _

theorem bil_deckRho (A : SL(2, ℤ)) (X Y : DeckSpace N) :
    bil (deckRho N A X) (deckRho N A Y) = bil X Y := by
  unfold bil
  simp only [deckRho_apply]
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N)) (fun q => X q * Y q)

theorem bil_symm_deckRho_left (A : SL(2, ℤ)) (X Y : DeckSpace N) :
    bil ((deckRho N A).symm X) Y = bil X (deckRho N A Y) := by
  conv_rhs => rw [← (deckRho N A).apply_symm_apply X]
  rw [bil_deckRho]

theorem bil_deckRho_T_right {X : DeckSpace N} (hX : deckRho N ModularGroup.T X = X) (n : ℤ)
    (Y : DeckSpace N) : bil X (deckRho N (ModularGroup.T ^ n) Y) = bil X Y := by
  conv_lhs => rw [← deckRho_T_zpow hX n]
  exact bil_deckRho _ X Y

/-! ## The scattering operator preserves `V_∞` -/

theorem mk_eq_mk_apply_one_zero {x y : SL(2, ℤ)} (h : (QuotientGroup.mk x : Deck N) = QuotientGroup.mk y) :
    ((x 1 0 : ℤ) : ZMod (N + 1)) = y 1 0 := by
  rw [deckMk_eq_iff] at h
  have := congrArg (fun A : SL(2, ZMod (N + 1)) => (A : Matrix (Fin 2) (Fin 2) (ZMod (N + 1))) 1 0) h
  simpa only [redL_apply] using this

theorem phiExt_congr {σ σ' : SL(2, ℤ)} (h : ((σ 1 0 : ℤ) : ZMod (N + 1)) = σ' 1 0) (s : ℂ) :
    SelbergEisensteinCriticalLine.phiExt (N + 1) σ s = SelbergEisensteinCriticalLine.phiExt (N + 1) σ' s := by
  unfold SelbergEisensteinCriticalLine.phiExt SelbergEisensteinCuspScattering.PhiS
  rw [h]

theorem phiExt_out_mul_T (g : Deck N) (s : ℂ) :
    SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out (g * QuotientGroup.mk ModularGroup.T)) s =
      SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s := by
  refine phiExt_congr ?_ s
  have h : (QuotientGroup.mk (Quotient.out (g * QuotientGroup.mk ModularGroup.T) : SL(2, ℤ)) : Deck N) =
      QuotientGroup.mk (Quotient.out g * ModularGroup.T) := by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [mk_eq_mk_apply_one_zero h]
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]

theorem mk_neg_one_comm (g : Deck N) :
    (QuotientGroup.mk (-1 : SL(2, ℤ)) : Deck N) * g = g * QuotientGroup.mk (-1 : SL(2, ℤ)) := by
  induction g using QuotientGroup.induction_on with
  | H x => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, neg_one_mul, mul_neg_one]

theorem scatVec_isCuspVec {v : DeckSpace N} (hv : IsCuspVec v) (s : ℂ) : IsCuspVec (scatVec s v) := by
  constructor
  · ext q
    rw [deckRho_apply, scatVec_apply, scatVec_apply]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk ModularGroup.T : Deck N))]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Equiv.coe_mulRight]
    congr 1
    · exact phiExt_out_mul_T g s
    · rw [mul_inv_rev, ← mul_assoc, mul_assoc q, mul_inv_cancel, mul_one]
  · ext q
    rw [deckRho_apply, scatVec_apply, scatVec_apply]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    have h := congrArg (fun w : DeckSpace N => w (q * g⁻¹)) hv.2
    simp only [deckRho_apply] at h
    rw [← h, mul_assoc, mul_assoc, ← mk_neg_one_comm]

/-! ## Horocycle averages of the deck Eisenstein series -/

theorem continuous_deck_of_coords {X : Type*} [TopologicalSpace X] {F : X → DeckSpace N}
    (h : ∀ q, Continuous fun x => F x q) : Continuous F := by
  have e : F = fun x => WithLp.toLp 2 (fun q => F x q) := funext fun x => rfl
  rw [e]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

theorem continuous_eisVec {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) : Continuous (eisVec s v) := by
  refine continuous_deck_of_coords fun q => ?_
  simp_rw [eisVec_apply_eq_sum hs hv]
  refine continuous_const.mul (continuous_finsetSum _ fun g _ => continuous_const.mul ?_)
  exact (SelbergPoincareBounded.continuous_poincare (N + 1) 0 hs).comp (continuous_modular_smul _)

/-- For continuous deck-equivariant `G` and `v ∈ V_T`, `(N+1) ∫_0^1 ⟨v, G⟩_β` is the pairing of `v`
with the level horocycle integrals of the coordinates. -/
theorem natCast_mul_intervalIntegral_bil {G : ℍ → DeckSpace N} (hGc : Continuous G)
    (hGe : deckEquivariant N G) {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v)
    {y : ℝ} (hy : 0 < y) :
    ((N + 1 : ℕ) : ℂ) * ∫ x in (0 : ℝ)..1, bil v (G (ofComplex (SelbergMaassMean.point x y))) =
      ∑ q : Deck N, v q * ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        G (ofComplex (SelbergMaassMean.point x y)) q := by
  have hcoord : ∀ q, Continuous fun x : ℝ => G (ofComplex (SelbergMaassMean.point x y)) q := fun q =>
    (PiLp.continuous_apply 2 _ q).comp (hGc.comp (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy))
  have hgc : Continuous fun x : ℝ => bil v (G (ofComplex (SelbergMaassMean.point x y))) :=
    continuous_finsetSum _ fun q _ => continuous_const.mul (hcoord q)
  have hper : Function.Periodic (fun x : ℝ => bil v (G (ofComplex (SelbergMaassMean.point x y)))) 1 := by
    intro x
    have h := apply_ofComplex_point_add_int hGe hy 1 x
    simp only [Int.cast_one] at h
    change bil v (G (ofComplex (SelbergMaassMean.point (x + 1) y))) =
      bil v (G (ofComplex (SelbergMaassMean.point x y)))
    rw [h, bil_deckRho_T_right hv]
  have h1 := hper.intervalIntegral_add_zsmul_eq ((N + 1 : ℕ) : ℤ) 0
    fun t₁ t₂ => hgc.intervalIntegrable _ _
  simp only [zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast] at h1
  rw [← h1]
  unfold bil
  rw [intervalIntegral.integral_finsetSum fun q _ => ((hcoord q).const_mul _).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun q _ => intervalIntegral.integral_const_mul _ _

/-- The level horocycle integrals of the coordinates of the deck Eisenstein series. -/
theorem intervalIntegral_eisVec_apply {s : ℂ} (hs : 1 < s.re) {w : DeckSpace N}
    (hw : IsCuspVec w) {y : ℝ} (hy : 0 < y) (q : Deck N) :
    ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), eisVec s w (ofComplex (SelbergMaassMean.point x y)) q =
      ((N + 1 : ℕ) : ℂ) * (((y : ℝ) : ℂ) ^ s * w q + ((y : ℝ) : ℂ) ^ (1 - s) * scatVec s w q) := by
  have hL' : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  simp_rw [eisVec_apply_eq_sum hs hw.1]
  have hint : ∀ g ∈ (Finset.univ : Finset (Deck N)), IntervalIntegrable (fun x : ℝ =>
      w (q * g⁻¹) * SelbergPoincare.poincare (N + 1) 0 s
        ((Quotient.out g : SL(2, ℤ)) • ofComplex (SelbergMaassMean.point x y))) volume 0
        ((N + 1 : ℕ) : ℝ) := fun g _ =>
    (continuous_const.mul ((SelbergPoincareBounded.continuous_poincare (N + 1) 0 hs).comp
      ((continuous_modular_smul _).comp
        (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hint]
  have hc : ∀ g : Deck N, ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), w (q * g⁻¹) *
      SelbergPoincare.poincare (N + 1) 0 s ((Quotient.out g : SL(2, ℤ)) • ofComplex (SelbergMaassMean.point x y)) =
      w (q * g⁻¹) * (((N + 1 : ℕ) : ℂ) * ((y : ℝ) : ℂ) ^ s *
        (SelbergEisensteinCuspConstant.count0 (N + 1) (Quotient.out g) : ℂ) +
        SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s * ((y : ℝ) : ℂ) ^ (1 - s)) := by
    intro g
    rw [intervalIntegral.integral_const_mul,
      SelbergEisensteinScatteringEntry.integral_poincare_cusp_phi (N + 1) _ hs hy,
      SelbergEisensteinCriticalLine.phiσ_eq_phiExt (N + 1) _ (by linarith)]
  rw [Finset.sum_congr rfl fun g _ => hc g]
  have e1 : ∑ g : Deck N, w (q * g⁻¹) * (((N + 1 : ℕ) : ℂ) * ((y : ℝ) : ℂ) ^ s *
      (SelbergEisensteinCuspConstant.count0 (N + 1) (Quotient.out g) : ℂ) +
      SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s * ((y : ℝ) : ℂ) ^ (1 - s)) =
      ((N + 1 : ℕ) : ℂ) * ((y : ℝ) : ℂ) ^ s * (2 * (N + 1 : ℂ) * w q) +
        ((y : ℝ) : ℂ) ^ (1 - s) * ∑ g : Deck N,
          SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s * w (q * g⁻¹) := by
    rw [← sum_count0 hw q, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [e1, scatVec_apply]
  push_cast
  field_simp

/-- **The constant term of the deck Eisenstein series** (`Re s > 1`, `v ∈ V_T`, `w ∈ V_∞`):
`∫_0^1 ⟨v, Ẽ(x + iy, s; w)⟩_β dx = ⟨v, y^s w + y^{1-s} Φ̃(s) w⟩_β`. -/
theorem intervalIntegral_bil_eisVec {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) {w : DeckSpace N} (hw : IsCuspVec w) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, bil v (eisVec s w (ofComplex (SelbergMaassMean.point x y))) =
      bil v (((y : ℝ) : ℂ) ^ s • w + ((y : ℝ) : ℂ) ^ (1 - s) • scatVec s w) := by
  have hL : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have h := natCast_mul_intervalIntegral_bil (continuous_eisVec hs hw.1) (deckEquivariant_eisVec hw.1)
    hv hy
  simp_rw [intervalIntegral_eisVec_apply hs hw hy] at h
  refine mul_left_cancel₀ hL (h.trans ?_)
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ## The truncated deck Eisenstein series -/

/-- **The truncation** `Λ^Y Ẽ(z, s; v) = Ẽ − [y > Y](y^s v + y^{1-s} Φ̃(s) v)`. -/
def eisTrunc (Y : ℝ) (s : ℂ) (v : DeckSpace N) (z : ℍ) : DeckSpace N :=
  eisExt s v z - if Y < z.im then ((z.im : ℂ) ^ s • v + (z.im : ℂ) ^ (1 - s) • scatVec s v) else 0

/-- One term of the truncated row sum. -/
def truncRowTerm (Y : ℝ) (s : ℂ) (v : DeckSpace N) (p : gammaSet 1 1 0) (z : ℍ) : DeckSpace N :=
  if RHTower.rowHeight p z ≤ Y then eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z else 0

theorem symm_deckRho_of_first_zero {v : DeckSpace N} (hv : IsCuspVec v) {p : gammaSet 1 1 0}
    (hp : p.1 0 = 0) : (deckRho N (gammaSetMatrix p)).symm v = v := by
  rcases (RHTower.first_zero_iff p).1 hp with rfl | rfl
  · obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix RHTower.rowPlus) 1
      (by simp [RHTower.rowPlus]) (by simp [RHTower.rowPlus])
    refine symm_eq_of_apply_eq ?_
    rw [hn, mul_one, deckRho_T_zpow hv.1]
  · obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix RHTower.rowMinus) (-1)
      (by simp [RHTower.rowMinus]) (by simp [RHTower.rowMinus])
    refine symm_eq_of_apply_eq ?_
    rw [hn, deckRho_mul, hv.2, deckRho_T_zpow hv.1]

/-- **The truncated row sum on `𝒟`** (`Re s > 1`, `Y ≥ 1`, `v ∈ V_∞`). -/
theorem eisTrunc_eq_truncRowSum (hN : 2 ≤ N) {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : IsCuspVec v) {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ fd) :
    eisTrunc Y s v z = (1 / 2 : ℂ) • ∑' p, truncRowTerm Y s v p z -
      if Y < z.im then (z.im : ℂ) ^ (1 - s) • scatVec s v else 0 := by
  have hsum := summable_eisTerm_cpow hs v z
  have hsplit : ∀ p, eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z = truncRowTerm Y s v p z +
      if Y < RHTower.rowHeight p z then eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z else 0 := by
    intro p
    unfold truncRowTerm
    by_cases h : RHTower.rowHeight p z ≤ Y
    · rw [if_pos h, if_neg (not_lt.2 h), add_zero]
    · rw [if_neg h, if_pos (not_le.1 h), zero_add]
  have hs1 : Summable fun p => truncRowTerm Y s v p z :=
    Summable.of_norm_bounded (hsum.norm) fun p => by
      unfold truncRowTerm; split_ifs <;> simp
  have hs2 : Summable fun p => if Y < RHTower.rowHeight p z then
      eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z else 0 :=
    Summable.of_norm_bounded (hsum.norm) fun p => by split_ifs <;> simp
  have htop : (∑' p, if Y < RHTower.rowHeight p z then eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z else 0) =
      if Y < z.im then (2 : ℂ) • ((z.im : ℂ) ^ s • v) else 0 := by
    rw [tsum_eq_sum (s := {RHTower.rowPlus, RHTower.rowMinus}) fun p hp => ?_]
    · rw [Finset.sum_pair RHTower.rowPlus_ne_rowMinus]
      have hP : RHTower.rowHeight RHTower.rowPlus z = z.im := RHTower.rowHeight_rowPlus z
      have hM : RHTower.rowHeight RHTower.rowMinus z = z.im := RHTower.rowHeight_rowMinus z
      rw [hP, hM]
      split_ifs
      · simp only [eisTerm]
        rw [symm_deckRho_of_first_zero hv (by simp [RHTower.rowPlus]),
          symm_deckRho_of_first_zero hv (by simp [RHTower.rowMinus])]
        change ((RHTower.rowHeight RHTower.rowPlus z : ℂ)) ^ s • v +
          ((RHTower.rowHeight RHTower.rowMinus z : ℂ)) ^ s • v = _
        rw [hP, hM, two_smul]
      · simp
    · have hp0 : p.1 0 ≠ 0 := by
        intro h0
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
        rcases (RHTower.first_zero_iff p).1 h0 with h | h
        · exact hp.1 h
        · exact hp.2 h
      rw [if_neg (not_lt.2 ((RHTower.rowHeight_le_one_of_mem_fd hz hp0).trans hY))]
  unfold eisTrunc
  rw [← eisVec_eq_eisExt hN hs hv, eisVec, incEis, tsum_congr hsplit, hs1.tsum_add hs2, htop]
  split_ifs
  · rw [smul_add, smul_smul]
    norm_num
    abel
  · simp

end

end GaloisForLFunctions.RHTower.DeckPointPair
