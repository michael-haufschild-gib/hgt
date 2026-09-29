import GaloisForLFunctions.RHTower.DeckCuspidalOrthogonalEisenstein
import GaloisForLFunctions.RHTower.EisensteinTruncatedRowSum
import GaloisForLFunctions.RHTower.SelbergEisensteinCriticalLine
import GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount

/-!
# The deck Eisenstein series and its coordinates

For `Re s > 1` and a deck vector `v` fixed by the translation `T`, the deck Eisenstein series is
`Ẽ(z, s; v) = ½ Σ_{(c, d) coprime} Im(M_{c,d} z)^s ρ(M_{c,d})⁻¹ v`, the incomplete Eisenstein series
of the profile `y ↦ y^s` (halved, so that `±(c, d)` count once).  It is absolutely convergent and
deck-equivariant.

Write `L = N + 1`.  The deck classes `g` with a prescribed bottom row modulo `L` are exactly the
`L` classes `T^n g₀`, `n < L`.  Averaging the coordinate `v(q [M_{c,d}]⁻¹)` over these classes
regroups the series by bottom rows modulo `L`, and the rows congruent to the bottom row of `σ` sum
to the `Γ(L)` Eisenstein series `E_∞(σ z, s)`.  Hence
`Ẽ(z, s; v)_q = (2L)⁻¹ Σ_{g ∈ Deck} v(q g⁻¹) E_∞(g z, s)`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## Deck classes and bottom rows modulo the level -/

local instance gammaNormalDES (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-- Reduction modulo the level `N + 1`. -/
abbrev redL (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod (N + 1)) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N + 1)))

theorem deckMk_eq_iff (A B : SL(2, ℤ)) :
    (QuotientGroup.mk A : Deck N) = QuotientGroup.mk B ↔ redL N A = redL N B := by
  rw [QuotientGroup.eq, CongruenceSubgroup.Gamma_mem', map_mul, map_inv, inv_mul_eq_one, eq_comm]

theorem redL_apply (A : SL(2, ℤ)) (i j : Fin 2) :
    (redL N A : Matrix (Fin 2) (Fin 2) (ZMod (N + 1))) i j = ((A i j : ℤ) : ZMod (N + 1)) := rfl

theorem deckRho_symm_apply (M : SL(2, ℤ)) (v : DeckSpace N) (q : Deck N) :
    (deckRho N M).symm v q = v (q * (QuotientGroup.mk M : Deck N)⁻¹) := by
  rw [← deckRho_inv]
  rfl

theorem deckRho_apply (M : SL(2, ℤ)) (v : DeckSpace N) (q : Deck N) :
    deckRho N M v q = v (q * (QuotientGroup.mk M : Deck N)) := rfl

/-- Two matrices with the same bottom row modulo the level differ by a power of `T` in the deck. -/
theorem exists_deckMk_eq_T_pow_mul {A B : SL(2, ℤ)}
    (h0 : ((A 1 0 : ℤ) : ZMod (N + 1)) = B 1 0) (h1 : ((A 1 1 : ℤ) : ZMod (N + 1)) = B 1 1) :
    ∃ n : ℕ, n < N + 1 ∧
      (QuotientGroup.mk A : Deck N) = QuotientGroup.mk (ModularGroup.T ^ (n : ℤ) * B) := by
  set b : ZMod (N + 1) := ((A 0 1 : ℤ) : ZMod (N + 1)) * B 0 0 - ((A 0 0 : ℤ) : ZMod (N + 1)) * B 0 1
  refine ⟨b.val, ZMod.val_lt b, ?_⟩
  rw [deckMk_eq_iff]
  have hA : ((A 0 0 : ℤ) : ZMod (N + 1)) * A 1 1 - ((A 0 1 : ℤ) : ZMod (N + 1)) * A 1 0 = 1 := by
    have := A.2; rw [Matrix.det_fin_two] at this; exact_mod_cast congrArg (Int.cast (R := ZMod (N + 1))) this
  have hB : ((B 0 0 : ℤ) : ZMod (N + 1)) * B 1 1 - ((B 0 1 : ℤ) : ZMod (N + 1)) * B 1 0 = 1 := by
    have := B.2; rw [Matrix.det_fin_two] at this; exact_mod_cast congrArg (Int.cast (R := ZMod (N + 1))) this
  have hbv : ((b.val : ℤ) : ZMod (N + 1)) = b := by simp
  ext i j
  rw [redL_apply, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    redL_apply, redL_apply, redL_apply, redL_apply]
  simp only [coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_one, Int.cast_zero,
    one_mul, zero_mul, zero_add, hbv]
  · simp only [b]
    linear_combination (-((A 0 0 : ℤ) : ZMod (N + 1))) * hB + ((B 0 0 : ℤ) : ZMod (N + 1)) * hA -
      ((A 0 0 : ℤ) : ZMod (N + 1)) * ((B 0 0 : ℤ) : ZMod (N + 1)) * h1 +
      ((A 0 1 : ℤ) : ZMod (N + 1)) * ((B 0 0 : ℤ) : ZMod (N + 1)) * h0
  · simp only [b]
    linear_combination (-((A 0 1 : ℤ) : ZMod (N + 1))) * hB + ((B 0 1 : ℤ) : ZMod (N + 1)) * hA +
      ((A 0 1 : ℤ) : ZMod (N + 1)) * ((B 0 1 : ℤ) : ZMod (N + 1)) * h0 -
      ((A 0 0 : ℤ) : ZMod (N + 1)) * ((B 0 1 : ℤ) : ZMod (N + 1)) * h1
  · simpa using h0
  · simpa using h1

theorem deckMk_T_pow_injective {n m : ℕ} (hn : n < N + 1) (hm : m < N + 1)
    (h : (QuotientGroup.mk (ModularGroup.T ^ (n : ℤ)) : Deck N) = QuotientGroup.mk (ModularGroup.T ^ (m : ℤ))) :
    n = m := by
  rw [deckMk_eq_iff] at h
  have h01 := congrArg (fun A : SL(2, ZMod (N + 1)) => (A : Matrix (Fin 2) (Fin 2) (ZMod (N + 1))) 0 1) h
  simp only [redL_apply, coe_T_zpow, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h01
  push_cast at h01
  have := (ZMod.natCast_eq_natCast_iff' n m (N + 1)).1 h01
  rwa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this

theorem bottomRow_redL_of_deckMk_eq {A B : SL(2, ℤ)} {n : ℤ}
    (h : (QuotientGroup.mk A : Deck N) = QuotientGroup.mk (ModularGroup.T ^ n * B)) (j : Fin 2) :
    ((A 1 j : ℤ) : ZMod (N + 1)) = B 1 j := by
  rw [deckMk_eq_iff] at h
  have hj := congrArg (fun C : SL(2, ZMod (N + 1)) => (C : Matrix (Fin 2) (Fin 2) (ZMod (N + 1))) 1 j) h
  simp only [redL_apply] at hj
  rw [hj, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_T_zpow]
  simp

open Classical in
/-- **Counting deck classes by bottom row.** For `f` invariant under left translation by `T`,
`Σ_g [row(g) ≡ row(M)] f(g) = L f([M])`. -/
theorem sum_deck_bottomRow (M : SL(2, ℤ)) (f : Deck N → ℂ)
    (hf : ∀ (n : ℤ) (g : Deck N), f (QuotientGroup.mk (ModularGroup.T ^ n) * g) = f g) :
    ∑ g : Deck N, (if (((Quotient.out g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (N + 1)) = M 1 0 ∧
      (((Quotient.out g : SL(2, ℤ)) 1 1 : ℤ) : ZMod (N + 1)) = M 1 1 then f g else 0) =
      (N + 1 : ℂ) * f (QuotientGroup.mk M) := by
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (fun g : Deck N =>
      (((Quotient.out g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (N + 1)) = M 1 0 ∧
      (((Quotient.out g : SL(2, ℤ)) 1 1 : ℤ) : ZMod (N + 1)) = M 1 1) =
      (Finset.range (N + 1)).image (fun n : ℕ =>
        (QuotientGroup.mk (ModularGroup.T ^ (n : ℤ)) : Deck N) * QuotientGroup.mk M) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, h1⟩
      obtain ⟨n, hn, hg⟩ := exists_deckMk_eq_T_pow_mul h0 h1
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.mk_mul, ← hg]
      exact QuotientGroup.out_eq' g
    · rintro ⟨n, _, rfl⟩
      have hg : (QuotientGroup.mk (Quotient.out ((QuotientGroup.mk (ModularGroup.T ^ (n : ℤ)) : Deck N) *
          QuotientGroup.mk M) : SL(2, ℤ)) : Deck N) = QuotientGroup.mk (ModularGroup.T ^ (n : ℤ) * M) := by
        rw [QuotientGroup.out_eq', QuotientGroup.mk_mul]
      exact ⟨bottomRow_redL_of_deckMk_eq hg 0, bottomRow_redL_of_deckMk_eq hg 1⟩
  rw [hset, Finset.sum_image]
  · simp only [hf]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  · intro n hn m hm h
    simp only [Finset.coe_range, Set.mem_Iio] at hn hm
    exact deckMk_T_pow_injective hn hm (mul_right_cancel h)

/-! ## The deck Eisenstein series -/

/-- **The deck Eisenstein series** `Ẽ(z, s; v) = ½ Σ_{(c,d)} Im(M_{c,d} z)^s ρ(M_{c,d})⁻¹ v`. -/
def eisVec (s : ℂ) (v : DeckSpace N) (z : ℍ) : DeckSpace N :=
  (1 / 2 : ℂ) • incEis (fun y : ℝ => (y : ℂ) ^ s) v z

theorem eisVec_smul {s : ℂ} {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) (A : SL(2, ℤ))
    (z : ℍ) : eisVec s v (A • z) = deckRho N A (eisVec s v z) := by
  rw [eisVec, incEis_smul hv, eisVec, map_smul]

theorem deckEquivariant_eisVec {s : ℂ} {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) :
    deckEquivariant N (eisVec s v) :=
  fun A z => eisVec_smul hv A z

theorem norm_eisTerm_cpow (s : ℂ) (v : DeckSpace N) (p : gammaSet 1 1 0) (z : ℍ) :
    ‖eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z‖ = RHTower.rowHeight p z ^ s.re * ‖v‖ := by
  rw [eisTerm, norm_smul, LinearIsometryEquiv.norm_map,
    Complex.norm_cpow_eq_rpow_re_of_pos (gammaSetMatrix p • z).im_pos]
  rfl

theorem summable_rowHeight_rpow {σ : ℝ} (hσ : 1 < σ) (z : ℍ) :
    Summable fun p : gammaSet 1 1 0 => RHTower.rowHeight p z ^ σ := by
  have h := RHTower.summable_rowHeight_cpow (s := (σ : ℂ)) (by simpa using hσ) z
  refine (Complex.summable_ofReal.1 (h.congr fun p => ?_))
  rw [Complex.ofReal_cpow (RHTower.rowHeight_pos p z).le]

theorem summable_eisTerm_cpow {s : ℂ} (hs : 1 < s.re) (v : DeckSpace N) (z : ℍ) :
    Summable fun p => eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z :=
  Summable.of_norm ((summable_rowHeight_rpow hs z).mul_right ‖v‖ |>.congr fun p =>
    (norm_eisTerm_cpow s v p z).symm)

theorem norm_eisVec_le {s : ℂ} (hs : 1 < s.re) (v : DeckSpace N) (z : ℍ) :
    ‖eisVec s v z‖ ≤ 1 / 2 * ((∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ s.re) * ‖v‖) := by
  rw [eisVec, norm_smul, incEis]
  have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (norm_tsum_le_tsum_norm ((summable_rowHeight_rpow hs z).mul_right ‖v‖ |>.congr fun p =>
    (norm_eisTerm_cpow s v p z).symm)).trans (le_of_eq ?_)
  simp_rw [norm_eisTerm_cpow]
  exact tsum_mul_right

/-! ## Coordinates -/

theorem eisVec_apply {s : ℂ} (hs : 1 < s.re) (v : DeckSpace N) (z : ℍ) (q : Deck N) :
    eisVec s v z q = (1 / 2 : ℂ) * ∑' p : gammaSet 1 1 0,
      (RHTower.rowHeight p z : ℂ) ^ s * v (q * (QuotientGroup.mk (gammaSetMatrix p) : Deck N)⁻¹) := by
  rw [eisVec, PiLp.smul_apply, smul_eq_mul, incEis]
  congr 1
  have h := (EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).map_tsum (summable_eisTerm_cpow hs v z)
  change EuclideanSpace.proj q (∑' p, eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z) = _
  rw [h]
  refine tsum_congr fun p => ?_
  change EuclideanSpace.proj q (eisTerm (fun y : ℝ => (y : ℂ) ^ s) v p z) = _
  rw [eisTerm, map_smul, smul_eq_mul]
  change (RHTower.rowHeight p z : ℂ) ^ s * (deckRho N (gammaSetMatrix p)).symm v q = _
  rw [deckRho_symm_apply]

/-- The row sum over bottom rows congruent to that of `σ` is the `Γ(L)` Eisenstein series `E_∞(σz, s)`. -/
theorem tsum_rowHeight_congr_eq_poincare (σ : SL(2, ℤ)) (s : ℂ) (z : ℍ) :
    ∑' p : gammaSet 1 1 0, (if ((p.1 0 : ℤ) : ZMod (N + 1)) = σ 1 0 ∧
      ((p.1 1 : ℤ) : ZMod (N + 1)) = σ 1 1 then (RHTower.rowHeight p z : ℂ) ^ s else 0) =
      SelbergPoincare.poincare (N + 1) 0 s (σ • z) := by
  rw [SelbergEisensteinCusp.poincare_smul_eq, SelbergEisensteinCusp.range_botσ]
  set S := SelbergEisensteinCusp.rowMul σ '' SelbergPoincareFourier.adm (N + 1)
  set e : gammaSet 1 1 0 → ℤ × ℤ := fun p => (p.1 0, p.1 1)
  have he : Function.Injective e := by
    intro p p' h
    simp only [e, Prod.mk.injEq] at h
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  rw [← he.tsum_eq (f := S.indicator (SelbergEisensteinCusp.esum s z))]
  · refine tsum_congr fun p => ?_
    have hcop : IsCoprime (p.1 0) (p.1 1) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact (gammaSet_one_mem_iff 1 p.1).1 p.2
    have hmem : e p ∈ S ↔ ((p.1 0 : ℤ) : ZMod (N + 1)) = σ 1 0 ∧
        ((p.1 1 : ℤ) : ZMod (N + 1)) = σ 1 1 := by
      rw [SelbergEisensteinCuspCount.mem_image_congr]
      simp only [e]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hcop⟩⟩
    by_cases hc : ((p.1 0 : ℤ) : ZMod (N + 1)) = σ 1 0 ∧ ((p.1 1 : ℤ) : ZMod (N + 1)) = σ 1 1
    · rw [if_pos hc, Set.indicator_of_mem (hmem.2 hc), SelbergEisensteinCusp.esum,
        RHTower.rowHeight_eq_div]
    · rw [if_neg hc, Set.indicator_of_notMem (fun h => hc (hmem.1 h))]
  · intro r hr
    have hrS : r ∈ S := by
      by_contra h
      exact hr (Set.indicator_of_notMem h _)
    obtain ⟨_, _, hcop⟩ := (SelbergEisensteinCuspCount.mem_image_congr _ σ r).1 hrS
    have hg : ((![r.1, r.2] : Fin 2 → ℤ) 0).gcd ((![r.1, r.2] : Fin 2 → ℤ) 1) = 1 := by
      simpa [Int.isCoprime_iff_gcd_eq_one] using hcop
    exact ⟨⟨![r.1, r.2], (gammaSet_one_mem_iff 1 _).2 hg⟩, by simp [e]⟩

open Classical in
/-- **Coordinates of the deck Eisenstein series** (`Re s > 1`):
`Ẽ(z, s; v)_q = (2L)⁻¹ Σ_{g ∈ Deck} v(q g⁻¹) E_∞(g z, s)`. -/
theorem eisVec_apply_eq_sum {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) (z : ℍ) (q : Deck N) :
    eisVec s v z q = (2 * (N + 1 : ℂ))⁻¹ * ∑ g : Deck N,
      v (q * g⁻¹) * SelbergPoincare.poincare (N + 1) 0 s ((Quotient.out g : SL(2, ℤ)) • z) := by
  have hL : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hinv : ∀ (n : ℤ) (g : Deck N),
      v (q * (QuotientGroup.mk (ModularGroup.T ^ n) * g)⁻¹) = v (q * g⁻¹) := by
    intro n g
    rw [mul_inv_rev, ← mul_assoc, ← QuotientGroup.mk_inv, ← deckRho_apply, ← zpow_neg,
      deckRho_T_zpow hv]
  have hcount : ∀ p : gammaSet 1 1 0, v (q * (QuotientGroup.mk (gammaSetMatrix p) : Deck N)⁻¹) =
      (N + 1 : ℂ)⁻¹ * ∑ g : Deck N, (if (((Quotient.out g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (N + 1)) =
        (gammaSetMatrix p) 1 0 ∧ (((Quotient.out g : SL(2, ℤ)) 1 1 : ℤ) : ZMod (N + 1)) =
        (gammaSetMatrix p) 1 1 then v (q * g⁻¹) else 0) := by
    intro p
    rw [sum_deck_bottomRow (gammaSetMatrix p) (fun g => v (q * g⁻¹)) hinv, ← mul_assoc,
      inv_mul_cancel₀ hL, one_mul]
  rw [eisVec_apply hs]
  simp_rw [hcount, Finset.mul_sum]
  have hsumm : ∀ g ∈ (Finset.univ : Finset (Deck N)), Summable fun p : gammaSet 1 1 0 =>
      (RHTower.rowHeight p z : ℂ) ^ s * ((N + 1 : ℂ)⁻¹ *
        (if (((Quotient.out g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (N + 1)) = (gammaSetMatrix p) 1 0 ∧
          (((Quotient.out g : SL(2, ℤ)) 1 1 : ℤ) : ZMod (N + 1)) = (gammaSetMatrix p) 1 1
          then v (q * g⁻¹) else 0)) := by
    intro g _
    refine Summable.of_norm_bounded ((summable_rowHeight_rpow hs z).mul_right ((N + 1 : ℝ)⁻¹ * ‖v‖))
      fun p => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (RHTower.rowHeight_pos p z), norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (RHTower.rowHeight_pos p z).le _)
    have hn : ‖(N + 1 : ℂ)⁻¹‖ = (N + 1 : ℝ)⁻¹ := by
      rw [norm_inv]; congr 1; exact_mod_cast Complex.norm_natCast (N + 1)
    rw [hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    split_ifs
    · exact PiLp.norm_apply_le _ _
    · rw [norm_zero]; exact norm_nonneg _
  rw [Summable.tsum_finsetSum hsumm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← tsum_rowHeight_congr_eq_poincare]
  simp only [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [gammaSetMatrix_apply_one_zero, gammaSetMatrix_apply_one_one]
  by_cases h : ((p.1 0 : ℤ) : ZMod (N + 1)) = ((Quotient.out g : SL(2, ℤ)) 1 0 : ℤ) ∧
      ((p.1 1 : ℤ) : ZMod (N + 1)) = ((Quotient.out g : SL(2, ℤ)) 1 1 : ℤ)
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    field_simp
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩]
    simp

end

end GaloisForLFunctions.RHTower.DeckPointPair
