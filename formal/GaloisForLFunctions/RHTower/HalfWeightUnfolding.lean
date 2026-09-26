import GaloisForLFunctions.RHTower.HalfWeightEisensteinContinuation
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding
import GaloisForLFunctions.RHTower.SelbergPoincareUnfolding

/-!
# Unfolding the weight-½ Eisenstein series of level `4M`

* `posRows`: the admissible bottom rows `(c, d)` (`4M ∣ c`, coprime) with `c > 0` or `(c,d) = (0,1)`,
  one for each pair `±(c,d)`; `rowMat p ∈ Γ₀(4M)` has bottom row `p`. Every `γ ∈ Γ₀(4M)` is
  `± T^k rowMat p` (`exists_sign_T_rowMat`), uniquely (`T_rowMat_eq_iff`).
* `repT (p, c) = rowMat p · out c`, `c ∈ Γ₀(4M) \ SL₂(ℤ)` (finitely many), represents the right cosets of
  the translations `⟨T⟩` in `PSL₂(ℤ)` (`repT_surj`, `repT_uniq`), so `⋃ repT(p,c) · 𝒟` is a fundamental
  domain for `⟨T⟩` (`isFundamentalDomain_repT`).
* `eisHalf_eq_two_tsum_pos`: for the trivial character and `Re w > 1`, `E(z,w) = 2 Σ_{p} F_z(p)`
  (the rows `±p` contribute equally).
* **`unfold_eisHalf`**: if `G(γz) = \overline{j(γ,z)} G(z)` on `Γ₀(4M)` (the transformation law of
  `\overline{θ(z)} y^{1/4}` times a `Γ₀(4M)`-invariant function) and `G(z) y^w` is integrable on the strip,
  then for `Re w > 1`
  `∫_𝒟 Σ_{c ∈ Γ₀(4M)\SL₂(ℤ)} G(out c · z) E(out c · z, w) dμ = 2 ∫_{0 ≤ Re z < 1} G(z) y^w dμ`.
-/

open Real Complex Filter Topology MeasureTheory UpperHalfPlane Set
open CongruenceSubgroup ModularGroup
open scoped MatrixGroups Pointwise

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.HTGeometry

noncomputable section

variable (M : ℕ)

/-! ### Representatives of `⟨T⟩ \ Γ₀(4M)` by positive bottom rows -/

/-- Admissible bottom rows `(c, d)` with `c > 0`, or `(c, d) = (0, 1)`. -/
def posRows : Set (ℤ × ℤ) := {p | p ∈ adm4 M ∧ (0 < p.1 ∨ (p.1 = 0 ∧ p.2 = 1))}

/-- A matrix with prescribed coprime bottom row. -/
def rowMat (p : posRows M) : SL(2, ℤ) := Classical.choose (exists_sl_bottom_row p.2.1.2)

theorem rowMat_10 (p : posRows M) : ent (rowMat M p) 1 0 = p.1.1 :=
  (Classical.choose_spec (exists_sl_bottom_row p.2.1.2)).1

theorem rowMat_11 (p : posRows M) : ent (rowMat M p) 1 1 = p.1.2 :=
  (Classical.choose_spec (exists_sl_bottom_row p.2.1.2)).2

theorem rowMat_mem (p : posRows M) : rowMat M p ∈ Gamma0 (4 * M) := by
  rw [Gamma0_mem]
  have h := p.2.1.1
  have : (ent (rowMat M p) 1 0 : ZMod (4 * M)) = 0 := by
    rw [rowMat_10, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  exact this

/-- Every `γ ∈ Γ₀(4M)` is `± T^k · rowMat p` for a positive row `p`. -/
theorem exists_sign_T_rowMat {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * M)) :
    ∃ (ε : SL(2, ℤ)) (k : ℤ) (p : posRows M), (ε = 1 ∨ ε = -1) ∧ γ = ε * (T ^ k * rowMat M p) := by
  set c := ent γ 1 0
  set d := ent γ 1 1
  have h4 : (4 * M : ℤ) ∣ c := by
    have := (Gamma0_mem.1 hγ)
    have h' : ((ent γ 1 0 : ℤ) : ZMod (4 * M)) = 0 := this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    exact_mod_cast h'
  have hcop : IsCoprime c d := by
    have hdet := det_entries γ
    exact ⟨-ent γ 0 1, ent γ 0 0, by simp only [c, d] at *; linarith⟩
  -- choose the sign
  obtain ⟨ε, hε, hpos⟩ : ∃ ε : SL(2, ℤ), (ε = 1 ∨ ε = -1) ∧
      (ent (ε * γ) 1 0, ent (ε * γ) 1 1) ∈ posRows M := by
    have hmem : ∀ ε : SL(2, ℤ), (ε = 1 ∨ ε = -1) →
        (ent (ε * γ) 1 0, ent (ε * γ) 1 1) ∈ adm4 M := by
      rintro ε (rfl | rfl)
      · simp only [one_mul]; exact ⟨h4, hcop⟩
      · rw [neg_one_mul, ent_neg, ent_neg]
        exact (mem_adm4_neg_iff M c d).2 ⟨h4, hcop⟩
    rcases lt_trichotomy c 0 with hc | hc | hc
    · refine ⟨-1, Or.inr rfl, hmem _ (Or.inr rfl), Or.inl ?_⟩
      rw [neg_one_mul, ent_neg]; linarith
    · have hd : d = 1 ∨ d = -1 := by
        have := hcop
        rw [hc] at this
        exact Int.isUnit_iff.1 (isCoprime_zero_left.1 this)
      rcases hd with hd | hd
      · exact ⟨1, Or.inl rfl, hmem _ (Or.inl rfl), Or.inr ⟨by simp [c] at hc ⊢; exact hc,
          by simp [d] at hd ⊢; exact hd⟩⟩
      · refine ⟨-1, Or.inr rfl, hmem _ (Or.inr rfl), Or.inr ⟨?_, ?_⟩⟩
        · show ent (-1 * γ) 1 0 = 0
          rw [neg_one_mul, ent_neg, show ent γ 1 0 = 0 from hc, neg_zero]
        · show ent (-1 * γ) 1 1 = 1
          rw [neg_one_mul, ent_neg, show ent γ 1 1 = -1 from hd, neg_neg]
    · exact ⟨1, Or.inl rfl, hmem _ (Or.inl rfl), Or.inl (by simpa using hc)⟩
  set p : posRows M := ⟨_, hpos⟩
  obtain ⟨k, hk⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (ε * γ) (rowMat M p)
    (by have := rowMat_10 M p; simp only [ent] at this; rw [this]; rfl)
    (by have := rowMat_11 M p; simp only [ent] at this; rw [this]; rfl)
  refine ⟨ε, k, p, hε, ?_⟩
  rcases hε with rfl | rfl
  · simpa using hk
  · rw [← hk]; simp

/-- Distinct positive rows, or distinct translations, give distinct `T^k rowMat p` up to sign. -/
theorem T_rowMat_eq_iff {k k' : ℤ} {p p' : posRows M}
    (h : T ^ k * rowMat M p = T ^ k' * rowMat M p' ∨ T ^ k * rowMat M p = -(T ^ k' * rowMat M p')) :
    k = k' ∧ p = p' := by
  have hrow : ∀ j : Fin 2, (T ^ k * rowMat M p) 1 j = (rowMat M p) 1 j :=
    T_zpow_mul_apply_one k _
  have hrow' : ∀ j : Fin 2, (T ^ k' * rowMat M p') 1 j = (rowMat M p') 1 j :=
    T_zpow_mul_apply_one k' _
  have h10 := rowMat_10 M p
  have h11 := rowMat_11 M p
  have h10' := rowMat_10 M p'
  have h11' := rowMat_11 M p'
  simp only [ent] at h10 h11 h10' h11'
  have hpp : p = p' := by
    rcases h with h | h
    · have e0 := congrArg (fun A : SL(2, ℤ) => A 1 0) h
      have e1 := congrArg (fun A : SL(2, ℤ) => A 1 1) h
      rw [hrow, hrow', h10, h10'] at e0
      rw [hrow, hrow', h11, h11'] at e1
      exact Subtype.ext (Prod.ext e0 e1)
    · exfalso
      have e0 := congrArg (fun A : SL(2, ℤ) => A 1 0) h
      have e1 := congrArg (fun A : SL(2, ℤ) => A 1 1) h
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at e0 e1
      rw [hrow, hrow', h10, h10'] at e0
      rw [hrow, hrow', h11, h11'] at e1
      rcases p.2.2 with hp | ⟨hp0, hp1⟩ <;> rcases p'.2.2 with hq | ⟨hq0, hq1⟩
      · linarith
      · linarith
      · linarith
      · linarith
  subst hpp
  refine ⟨?_, rfl⟩
  rcases h with h | h
  · exact T_zpow_injective (mul_right_cancel h)
  · exfalso
    have e1 := congrArg (fun A : SL(2, ℤ) => A 1 1) h
    have e0 := congrArg (fun A : SL(2, ℤ) => A 1 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at e0 e1
    rw [hrow, hrow', h10] at e0
    rw [hrow, hrow', h11] at e1
    rcases p.2.2 with hp | ⟨hp0, hp1⟩
    · linarith
    · linarith


/-! ### Representatives of `⟨T⟩ \ PSL₂(ℤ)` through `Γ₀(4M)` -/

/-- Right cosets `Γ₀(4M) \ SL₂(ℤ)`. -/
abbrev Cos0 := Quotient (QuotientGroup.rightRel (Gamma0 (4 * M)))

instance [NeZero M] : Finite (Cos0 M) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Gamma0 (4 * M))).symm

noncomputable instance [NeZero M] : Fintype (Cos0 M) := Fintype.ofFinite _

/-- The representative `rowMat p · out(c)` of a coset of translations in `PSL₂(ℤ)`. -/
def repT (ic : posRows M × Cos0 M) : PSL2Z :=
  QuotientGroup.mk (rowMat M ic.1 * Quotient.out ic.2)

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 (4 * M) := by
  rw [Gamma0_mem]; simp

theorem repT_surj (g : PSL2Z) : ∃ (h : translationSubgroup) (ic : posRows M × Cos0 M),
    (h : PSL2Z) * repT M ic = g := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  set c : Cos0 M := Quotient.mk _ γ
  have hc : QuotientGroup.rightRel (Gamma0 (4 * M)) (Quotient.out c) γ := Quotient.mk_out (s := _) γ
  have hα : γ * (Quotient.out c)⁻¹ ∈ Gamma0 (4 * M) := QuotientGroup.rightRel_apply.mp hc
  obtain ⟨ε, k, p, hε, hk⟩ := exists_sign_T_rowMat M hα
  refine ⟨⟨psl2zT ^ k, Subgroup.zpow_mem_zpowers _ _⟩, (p, c), ?_⟩
  have hγ : γ = ε * (T ^ k * rowMat M p * Quotient.out c) := by
    have e1 : γ = (γ * (Quotient.out c)⁻¹) * Quotient.out c := by group
    rw [e1, hk]; group
  simp only [repT]
  rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, hγ]
  rcases hε with rfl | rfl
  · rw [one_mul, mul_assoc]
  · rw [neg_one_mul, PSL2Z_mk_neg, mul_assoc]

theorem repT_uniq (h h' : translationSubgroup) (ic ic' : posRows M × Cos0 M)
    (e : (h : PSL2Z) * repT M ic = (h' : PSL2Z) * repT M ic') : h = h' ∧ ic = ic' := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
  obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp h'.2
  obtain ⟨p, c⟩ := ic
  obtain ⟨p', c'⟩ := ic'
  simp only [repT] at e
  rw [← hk, ← hk', ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, PSL2Z_mk_eq_iff] at e
  simp only [← mul_assoc] at e
  -- the `Γ₀(4M)`-cosets agree
  have hmem : ∀ x ∈ ({1, -1} : Set SL(2, ℤ)), Quotient.out c' * (Quotient.out c)⁻¹ =
      (T ^ k' * rowMat M p')⁻¹ * (x * (T ^ k * rowMat M p)) →
      Quotient.out c' * (Quotient.out c)⁻¹ ∈ Gamma0 (4 * M) := by
    intro x hx hxe
    rw [hxe]
    have hT : ∀ n : ℤ, T ^ n ∈ Gamma0 (4 * M) := fun n => zpow_mem (T_mem_Gamma0 M) n
    have hxm : x ∈ Gamma0 (4 * M) := by
      rcases hx with rfl | hx
      · exact one_mem _
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact neg_one_mem_Gamma0 M
    exact mul_mem (inv_mem (mul_mem (hT k') (rowMat_mem M p')))
      (mul_mem hxm (mul_mem (hT k) (rowMat_mem M p)))
  have hcc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    show QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply]
    rcases e with e | e
    · refine hmem 1 (by simp) ?_
      calc Quotient.out c' * (Quotient.out c)⁻¹
          = (T ^ k' * rowMat M p')⁻¹ * (T ^ k' * rowMat M p' * Quotient.out c') * (Quotient.out c)⁻¹ := by
            group
        _ = (T ^ k' * rowMat M p')⁻¹ * (T ^ k * rowMat M p * Quotient.out c) * (Quotient.out c)⁻¹ := by
            rw [e]
        _ = _ := by group
    · refine hmem (-1) (by simp) ?_
      have e' : T ^ k' * rowMat M p' * Quotient.out c' = -1 * (T ^ k * rowMat M p * Quotient.out c) := by
        rw [e, neg_one_mul]
      calc Quotient.out c' * (Quotient.out c)⁻¹
          = (T ^ k' * rowMat M p')⁻¹ * (T ^ k' * rowMat M p' * Quotient.out c') * (Quotient.out c)⁻¹ := by
            group
        _ = (T ^ k' * rowMat M p')⁻¹ * (-1 * (T ^ k * rowMat M p * Quotient.out c)) * (Quotient.out c)⁻¹ := by
            rw [e']
        _ = _ := by group
  subst hcc
  have e2 : T ^ k * rowMat M p = T ^ k' * rowMat M p' ∨ T ^ k * rowMat M p = -(T ^ k' * rowMat M p') := by
    rcases e with e | e
    · left; exact (mul_right_cancel e).symm
    · right
      have : T ^ k' * rowMat M p' = -(T ^ k * rowMat M p) := by
        have e' : T ^ k' * rowMat M p' * Quotient.out c = -(T ^ k * rowMat M p) * Quotient.out c := by
          rw [e]; simp
        exact mul_right_cancel e'
      rw [this, neg_neg]
  obtain ⟨hkk, hpp⟩ := T_rowMat_eq_iff M e2
  subst hkk; subst hpp
  refine ⟨Subtype.ext (by rw [← hk, ← hk']), rfl⟩

/-- `⋃ repT(p,c) • 𝒟` is a fundamental domain for the translations. -/
theorem isFundamentalDomain_repT [NeZero M] :
    IsFundamentalDomain translationSubgroup (⋃ ic, repT M ic • fd) volume :=
  isFundamentalDomain_iUnion_smul_of_cosetReps isFundamentalDomain_fd translationSubgroup (repT M)
    (repT_surj M) (repT_uniq M)

theorem repT_injective : Function.Injective (repT M) := fun ic ic' h =>
  (repT_uniq M 1 1 ic ic' (by rw [h])).2


/-! ### The Eisenstein series over positive rows -/

theorem posRows_subset : posRows M ⊆ adm4 M := fun _ hp => hp.1

theorem neg_mem_posRows_iff {p : ℤ × ℤ} (hp : p ∈ adm4 M) : -p ∈ posRows M ↔ p ∉ posRows M := by
  obtain ⟨c, d⟩ := p
  have hcop : IsCoprime c d := hp.2
  have hneg : (-c, -d) ∈ adm4 M := (mem_adm4_neg_iff M c d).2 hp
  simp only [posRows, Set.mem_setOf_eq, Prod.neg_mk, hneg, hp, true_and, not_or, not_and]
  constructor
  · rintro (h | ⟨h0, h1⟩)
    · exact ⟨by linarith, fun h0 => by linarith⟩
    · exact ⟨by linarith, fun _ => by linarith⟩
  · rintro ⟨h1, h2⟩
    rcases lt_or_eq_of_le (not_lt.1 h1) with h | h
    · left; linarith
    · right
      refine ⟨by rw [h]; simp, ?_⟩
      have hd : d = 1 ∨ d = -1 := by
        rw [h] at hcop; exact Int.isUnit_iff.1 (isCoprime_zero_left.1 hcop)
      rcases hd with hd | hd
      · exact absurd hd (h2 h)
      · rw [hd]; norm_num

theorem one_neg_one : (1 : DirichletCharacter ℂ (4 * M)) (-1) = 1 :=
  MulChar.one_apply isUnit_one.neg

/-- For the trivial character and `Re w > 1`: `E(z,w) = 2 Σ_{positive rows} F(p)`. -/
theorem eisHalf_eq_two_tsum_pos {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisHalf M (1 : DirichletCharacter ℂ (4 * M)) w z =
      2 * ∑' p : posRows M, Fp M (1 : DirichletCharacter ℂ (4 * M)) w z p := by
  set F := Fp M (1 : DirichletCharacter ℂ (4 * M)) w z
  have hS := summable_indicator M (1 : DirichletCharacter ℂ (4 * M)) hw z
  have hsum : ∀ s ⊆ adm4 M, Summable (s.indicator F) := by
    intro s hs
    refine Summable.of_norm_bounded hS fun p => ?_
    by_cases hp : p ∈ s
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hs hp)]
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact norm_nonneg _
  set N := adm4 M \ posRows M
  have hsplit : (adm4 M).indicator F = (posRows M).indicator F + N.indicator F := by
    funext p
    rw [Pi.add_apply]
    by_cases h1 : p ∈ posRows M
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (posRows_subset M h1),
        Set.indicator_of_notMem (fun h => h.2 h1), add_zero]
    · by_cases h2 : p ∈ adm4 M
      · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h1,
          Set.indicator_of_mem (show p ∈ N from ⟨h2, h1⟩), zero_add]
      · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h1,
          Set.indicator_of_notMem (fun h => h2 h.1), add_zero]
  have hneg : ∑' p : ℤ × ℤ, N.indicator F p = ∑' p : ℤ × ℤ, (posRows M).indicator F p := by
    rw [← (Equiv.neg (ℤ × ℤ)).tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [Equiv.neg_apply]
    by_cases hp : p ∈ posRows M
    · have h1 : -p ∈ N := by
        refine ⟨?_, ?_⟩
        · obtain ⟨c, d⟩ := p; exact (mem_adm4_neg_iff M c d).2 hp.1
        · intro h; exact (neg_mem_posRows_iff M hp.1).1 h hp
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hp]
      obtain ⟨c, d⟩ := p
      show F (-c, -d) = F (c, d)
      simp only [F]
      rw [Fp_neg, one_neg_one, map_one, one_mul]
    · have h1 : -p ∉ N := by
        rintro ⟨h1, h2⟩
        have hp' : p ∈ adm4 M := by
          obtain ⟨c, d⟩ := p; exact (mem_adm4_neg_iff M c d).1 h1
        exact hp (by have := (neg_mem_posRows_iff M h1).2 h2; simpa using this)
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hp]
  rw [eisHalf_eq_tsum_indicator, hsplit, Pi.add_def, (hsum _ (posRows_subset M)).tsum_add
    (hsum _ Set.sdiff_subset), hneg, ← tsum_subtype (posRows M) F, two_mul]


/-! ### Unfolding against the weight-½ Eisenstein series -/

theorem jU_one (z : UpperHalfPlane) : jU 1 z = 1 := by
  have h := jU_mul 1 1 z
  rw [one_mul, one_smul] at h
  have h1 : jU 1 z ≠ 0 := by
    intro h0; have := norm_jU 1 z; rw [h0, norm_zero] at this; exact zero_ne_one this
  have := mul_left_cancel₀ h1 (h.symm.trans (mul_one _).symm) |>.symm
  rw [this]

theorem jU_T_zpow (n : ℤ) (z : UpperHalfPlane) : jU (T ^ n) z = 1 := by
  have := jU_T_zpow_mul n 1 z
  rw [mul_one, jU_one] at this
  exact this

theorem repT_smul (ic : posRows M × Cos0 M) (z : UpperHalfPlane) :
    repT M ic • z = rowMat M ic.1 • (Quotient.out ic.2 • z) := by
  rw [repT, PSL2Z_mk_smul, mul_smul]

/-- The summand: `G(γ_p z) Im(γ_p z)^w = G(z) F_z(p)` for the trivial character. -/
theorem G_rowMat_eq {G : UpperHalfPlane → ℂ}
    (hG : ∀ γ ∈ Gamma0 (4 * M), ∀ z, G (γ • z) = starRingEnd ℂ (jU γ z) * G z)
    (w : ℂ) (z : UpperHalfPlane) (p : posRows M) :
    G (rowMat M p • z) * (((rowMat M p • z).im : ℝ) : ℂ) ^ w =
      G z * Fp M (1 : DirichletCharacter ℂ (4 * M)) w z p := by
  set γ : Gamma0 (4 * M) := ⟨rowMat M p, rowMat_mem M p⟩
  have he := eTerm_eq_Fp M (1 : DirichletCharacter ℂ (4 * M)) w z γ
  have h10 : ent γ 1 0 = p.1.1 := rowMat_10 M p
  have h11 : ent γ 1 1 = p.1.2 := rowMat_11 M p
  rw [h10, h11] at he
  rw [← he, eTerm, MulChar.one_apply (isUnit_d M γ), map_one, one_mul, hG _ (rowMat_mem M p)]
  ring

/-- **Rankin–Selberg unfolding for the weight-½ Eisenstein series.** Let `G` transform like
`\overline{θ} y^{1/4}`, i.e. `G(γz) = \overline{j(γ,z)} G(z)` on `Γ₀(4M)`, with `G(z) y^w` integrable on the
strip `0 ≤ Re z < 1`. Then for `Re w > 1`, with `out c` running over `Γ₀(4M) \ SL₂(ℤ)`,
`∫_𝒟 Σ_c G(out c · z) E(out c · z, w) dμ = 2 ∫_{strip} G(z) y^w dμ`. -/
theorem unfold_eisHalf [NeZero M] {w : ℂ} (hw : 1 < w.re) {G : UpperHalfPlane → ℂ}
    (hG : ∀ γ ∈ Gamma0 (4 * M), ∀ z, G (γ • z) = starRingEnd ℂ (jU γ z) * G z)
    (hint : IntegrableOn (fun z : UpperHalfPlane => G z * ((z.im : ℝ) : ℂ) ^ w) modularStrip) :
    ∫ z in fd, ∑ c : Cos0 M, G (Quotient.out c • z) *
        eisHalf M (1 : DirichletCharacter ℂ (4 * M)) w (Quotient.out c • z) =
      2 * ∫ z in modularStrip, G z * ((z.im : ℝ) : ℂ) ^ w := by
  set f : UpperHalfPlane → ℂ := fun z => G z * ((z.im : ℝ) : ℂ) ^ w with hf
  have hfinv : ∀ (h : translationSubgroup) (z : UpperHalfPlane), f (h • z) = f z := by
    intro h z
    obtain ⟨n, hn⟩ := translationSubgroup_smul_eq h z
    simp only [f]
    rw [hn, hG _ (zpow_mem (T_mem_Gamma0 M) n), jU_T_zpow, map_one, one_mul,
      UpperHalfPlane.modular_T_zpow_smul]
    simp
  have hU := isFundamentalDomain_repT M
  have hintU : IntegrableOn f (⋃ ic, repT M ic • fd) :=
    (hU.integrableOn_iff isFundamentalDomain_modularStrip hfinv).mpr hint
  rw [isFundamentalDomain_modularStrip.setIntegral_eq hU hfinv,
    SelbergPoincareUnfolding.integral_iUnion_eq_integral_tsum isFundamentalDomain_fd
      (repT_injective M) hintU, ← integral_const_mul]
  congr 1
  funext z
  -- the pointwise identity
  set g : Cos0 M × posRows M → ℂ := fun cp => f (repT M (cp.2, cp.1) • z)
  have hg : ∀ cp : Cos0 M × posRows M, g cp =
      G (Quotient.out cp.1 • z) * Fp M (1 : DirichletCharacter ℂ (4 * M)) w (Quotient.out cp.1 • z) cp.2 := by
    intro cp
    simp only [g, f, repT_smul]
    exact G_rowMat_eq M hG w _ cp.2
  have hslice : ∀ c : Cos0 M, Summable fun p : posRows M => ‖g (c, p)‖ := by
    intro c
    have hS := summable_indicator M (1 : DirichletCharacter ℂ (4 * M)) hw (Quotient.out c • z)
    have h2 : Summable fun p : posRows M =>
        ‖Fp M (1 : DirichletCharacter ℂ (4 * M)) w (Quotient.out c • z) p‖ :=
      (hS.subtype (posRows M)).congr fun p => by
        simp only [Function.comp, Set.indicator_of_mem (posRows_subset M p.2)]
    refine (h2.mul_left ‖G (Quotient.out c • z)‖).congr fun p => ?_
    rw [hg, norm_mul]
  have hgs : Summable g := by
    refine Summable.of_norm ?_
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨hslice, Summable.of_finite⟩
  have e1 : ∑' ic : posRows M × Cos0 M, f (repT M ic • z) = ∑' cp : Cos0 M × posRows M, g cp := by
    rw [← (Equiv.prodComm (Cos0 M) (posRows M)).tsum_eq]
    rfl
  rw [e1, hgs.tsum_prod, tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hg]
  rw [tsum_mul_left, eisHalf_eq_two_tsum_pos M hw]
  ring
