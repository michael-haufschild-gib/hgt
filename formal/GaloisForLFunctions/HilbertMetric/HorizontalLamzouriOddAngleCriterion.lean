import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriOddInterference

/-!
# The odd-angle criterion for mixed points

**Regrouping** (`HorizontalPacket.four_mass_bound_singleOwner`). For a pair `p`, move the even
vectors `g_q` of all other pairs into the real part, as heavy atoms of weight `2m_q ≥ 2`. These
cost nothing in the four-trace bound. The pair part becomes
`Φ_p = 2m_p g_p ⊗ g_p − Σ_q 2m_q h_q ⊗ h_q`, which has at most one positive eigenvalue, and
`4·mass − E − 2N + 2 Σ_{x∈M} ⟪Φ_p⁺ f_x, f_x⟫ ≤ Σ_H (2‖f‖² − 1) + Σ_M (2‖f‖² − 1)`.

**Odd-angle criterion** (`HorizontalPacket.four_mass_sub_energy_le_of_oddAngle`). Let every mixed
point `x` have an own pair `p(x)` in a set `O` of `r` pairs. Let `κ_x` bound the angle between
`g_{p(x)}` and the span of all odd vectors, `|⟪d, g_{p(x)}⟫| ≤ κ_x‖d‖` on `span{h_q}`. If
`2m_{p(x)} ((|⟪g_{p(x)}, f_x⟫| − κ_x‖f_x‖)⁺)² ≥ r (‖f_x‖² − ½)` for every mixed `x`, then
`4·mass − E − 2N ≤ #H`.

The proof averages the regrouped bound over `p ∈ O`. Owner `p(x)` gives
`⟪Φ_{p(x)}⁺ f_x, f_x⟫ ≥ 2m((|⟪g, f⟫| − κ‖f‖)⁺)²` by the scale-free decoupling theorem
(`positivePartForm_ge_of_oddInterference`), and the other owners contribute `≥ 0`.

Neither the odd vectors' sizes nor the other pairs' even vectors enter the criterion. Only the
angle `κ_x` between the own even vector and the odd span does, against the overlap `⟪g, f⟫`.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
  [DecidableEq ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP)

/-- The one-owner pair form `Q_p(v) = 2m_p⟪g_p, v⟫² − Σ_q 2m_q⟪h_q, v⟫²`. -/
def ownerForm (p : ιP) (v : V) : ℝ :=
  2 * P.mP p * ⟪P.g p, v⟫ ^ 2 - ∑ q, 2 * P.mP q * ⟪P.h q, v⟫ ^ 2

omit [Fintype ι₂] [Fintype ιH] [Fintype ιM] in
/-- `Σ_q F(q) = F(p) + Σ_{q ≠ p} F(q)`. -/
theorem sum_split_owner (p : ιP) (F : ιP → ℝ) :
    ∑ q, F q = F p + ∑ q : {q // q ≠ p}, F q.1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  congr 1
  exact Finset.sum_subtype _ (fun q => by simp) F

/-- **Regrouped bound for one owner.** -/
theorem four_mass_bound_singleOwner [FiniteDimensional ℝ V] (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ q, 1 ≤ P.mP q) (p : ιP) {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ V)
    (ev : Fin n → ℝ) (hd : ∀ v, P.ownerForm p v = ∑ j, ev j * ⟪e j, v⟫ ^ 2) :
    4 * P.mass - P.energy - 2 * P.count + 2 * ∑ x, positivePartForm e ev (P.fM x)
      ≤ ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) := by
  classical
  -- the regrouped families
  set cR : (ι₂ ⊕ ιH ⊕ ιM) ⊕ {q // q ≠ p} → ℝ :=
    Sum.elim P.realWeight fun q => 2 * P.mP q.1 with hcR
  set wR : (ι₂ ⊕ ιH ⊕ ιM) ⊕ {q // q ≠ p} → V := Sum.elim P.realVec fun q => P.g q.1 with hwR
  set cP : Unit ⊕ ιP → ℝ := Sum.elim (fun _ => 2 * P.mP p) fun q => -(2 * P.mP q) with hcP
  set wP : Unit ⊕ ιP → V := Sum.elim (fun _ => P.g p) P.h with hwP
  -- every functional of the atoms is unchanged by the regrouping
  have hregroup : ∀ F : V → ℝ, ∑ k, cR k * F (wR k) + ∑ l, cP l * F (wP l) =
      ∑ k, P.realWeight k * F (P.realVec k) + ∑ l, P.pairWeight l * F (P.pairVec l) := by
    intro F
    simp only [cR, wR, cP, wP, pairWeight, pairVec, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
    rw [sum_split_owner p fun q => 2 * P.mP q * F (P.g q)]
    ring
  have hform : ∀ ψ, weightedForm cR wR ψ + weightedForm cP wP ψ = P.diagForm ψ := fun ψ => by
    rw [P.diagForm_eq_split]
    simp only [weightedForm]
    exact hregroup fun x => ⟪x, ψ⟫ ^ 2
  have hc : ∀ k, cR k = 1 ∨ 2 ≤ cR k := by
    rintro ((i | j) | q)
    · exact Or.inr (hm₂ i)
    · exact Or.inl rfl
    · exact Or.inr (by have := hmP q.1; simp only [cR, Sum.elim_inr]; linarith)
  have hdP : ∀ v, weightedForm cP wP v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 := fun v => by
    rw [← hd, ownerForm]
    simp only [weightedForm, cP, wP, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
    ring
  have hcap : ∀ v, (∀ _u : Unit, ⟪P.g p, v⟫ = 0) → weightedForm cP wP v ≤ 0 := fun v hv => by
    rw [hdP, ← hd, ownerForm, hv ()]
    have := Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) =>
      mul_nonneg (by linarith [hmP q] : (0 : ℝ) ≤ 2 * P.mP q) (sq_nonneg ⟪P.h q, v⟫)
    nlinarith
  have hN : 2 * (Fintype.card Unit : ℝ) ≤ 2 * P.mP p := by
    rw [Fintype.card_unit, Nat.cast_one]; linarith [hmP p]
  set M : Finset ((ι₂ ⊕ ιH ⊕ ιM) ⊕ {q // q ≠ p}) :=
    Finset.univ.map ⟨fun x => Sum.inl (Sum.inr (Sum.inr x)), fun x y h => by simpa using h⟩
  have hMmem : ∀ k ∈ M, cR k = 1 := by
    intro k hk
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hk
    rfl
  have hmain := spectral_four_trace_bound_positivePart cR wR cP wP (fun _ : Unit => P.g p)
    (2 * P.mP p) e ev hdP hc hcap hN M hMmem
  have hmass : ∑ k, cR k * ‖wR k‖ ^ 2 + ∑ l, cP l * ‖wP l‖ ^ 2 = P.mass := by
    rw [hregroup fun v => ‖v‖ ^ 2]
    exact (P.sum_wt_mul_split fun v => ‖v‖ ^ 2).symm
  have henergy : ∑ k, cR k * (weightedForm cR wR (wR k) + weightedForm cP wP (wR k)) +
      ∑ l, cP l * (weightedForm cR wR (wP l) + weightedForm cP wP (wP l)) = P.energy := by
    simp only [hform]
    rw [hregroup P.diagForm, P.energy_eq_sum_diagForm, P.sum_wt_mul_split P.diagForm]
  have hcount : ∑ k, cR k + 2 * P.mP p = P.count := by
    have h1 := hregroup fun _ => (1 : ℝ)
    simp only [mul_one] at h1
    have h2 : ∑ l, cP l = 2 * P.mP p - ∑ q, 2 * P.mP q := by
      simp only [cP, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.sum_singleton, Finset.sum_neg_distrib]
      ring
    have h3 : ∑ l, P.pairWeight l = 0 := by
      simp only [pairWeight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_neg_distrib, add_neg_cancel]
    have h4 : ∑ k, P.realWeight k + 2 * ∑ q, P.mP q = P.count := by
      simp only [count, realWeight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_sum,
        Nat.cast_add]
      ring
    rw [h2, h3, add_zero] at h1
    rw [← h4, Finset.mul_sum]
    linarith
  have hslack : (∑ k, if cR k < 2 then 2 * ‖wR k‖ ^ 2 - 1 else 0) =
      ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) := by
    simp only [cR, wR, realWeight, realVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have h₂ : ∀ i, ¬ P.m₂ i < 2 := fun i => not_lt.mpr (hm₂ i)
    have hq : ∀ q : {q // q ≠ p}, ¬ 2 * P.mP q.1 < 2 := fun q =>
      not_lt.mpr (by linarith [hmP q.1])
    simp [h₂, hq]
  have hMsum : ∑ k ∈ M, positivePartForm e ev (wR k) = ∑ x, positivePartForm e ev (P.fM x) := by
    rw [Finset.sum_map]
    rfl
  have hb : 0 ≤ max (∑ l, cP l * ‖wP l‖ ^ 2 - 2 * (Fintype.card Unit : ℝ)) 0 ^ 2 /
      (Fintype.card Unit : ℝ) := by positivity
  rw [hmass, henergy, hcount, hslack, hMsum] at hmain
  linarith

/-- **Odd-angle criterion.** Let every mixed point `x` own a pair `own x` in a set `O` of `r`
pairs, and let `κ_x ≥ 0` satisfy `|⟪d, g_{own x}⟫| ≤ κ_x‖d‖` on the span of all odd vectors. If
`r (‖f_x‖² − 1/2) ≤ 2m_{own x} ((|⟪g_{own x}, f_x⟫| − κ_x‖f_x‖)⁺)²` for every mixed `x`, then
`4·mass − E − 2N ≤ #H`. -/
theorem four_mass_sub_energy_le_of_oddAngle [FiniteDimensional ℝ V] (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ q, 1 ≤ P.mP q) (hH : ∀ i, ‖P.fH i‖ ≤ 1) (own : ιM → ιP) (O : Finset ιP)
    (hO : ∀ x, own x ∈ O) (hOne : O.Nonempty) (κ : ιM → ℝ) (hκ0 : ∀ x, 0 ≤ κ x)
    (hκ : ∀ x, ∀ d ∈ Submodule.span ℝ (Set.range P.h), |⟪d, P.g (own x)⟫| ≤ κ x * ‖d‖)
    (hfree : ∀ x, (O.card : ℝ) * (‖P.fM x‖ ^ 2 - 1 / 2) ≤
      2 * P.mP (own x) * max (|⟪P.g (own x), P.fM x⟫| - κ x * ‖P.fM x‖) 0 ^ 2) :
    4 * P.mass - P.energy - 2 * P.count ≤ (Fintype.card ιH : ℝ) := by
  classical
  -- a diagonalisation of every owner form
  have hdiag : ∀ q : ιP, ∃ e : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V,
      ∃ ev : Fin (finrank ℝ V) → ℝ, ∀ v, P.ownerForm q v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 := by
    intro q
    obtain ⟨e, ev, h⟩ := exists_weightedForm_diag
      (Sum.elim (fun _ : Unit => 2 * P.mP q) fun q' => -(2 * P.mP q'))
      (Sum.elim (fun _ : Unit => P.g q) P.h)
    refine ⟨e, ev, fun v => ?_⟩
    rw [← h, ownerForm]
    simp only [weightedForm, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
    ring
  choose E Ev hE using hdiag
  set Pp : ιP → ιM → ℝ := fun q x => positivePartForm (E q) (Ev q) (P.fM x) with hPp
  -- one bound per owner
  set R := ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) with hR
  set A := 4 * P.mass - P.energy - 2 * P.count with hA
  have hone : ∀ q, A + 2 * ∑ x, Pp q x ≤ R := fun q =>
    P.four_mass_bound_singleOwner hm₂ hmP q (E q) (Ev q) (hE q)
  have hsum : (O.card : ℝ) * A + 2 * ∑ x, ∑ q ∈ O, Pp q x ≤ (O.card : ℝ) * R := by
    have := Finset.sum_le_sum fun q (_ : q ∈ O) => hone q
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      at this
    rw [Finset.sum_comm]
    linarith
  -- the own owner pays each mixed point
  have hPp0 : ∀ q x, 0 ≤ Pp q x := fun q x => positivePartForm_nonneg _ _ _
  have hpoint : ∀ x, (O.card : ℝ) * (2 * ‖P.fM x‖ ^ 2 - 1) ≤ 2 * ∑ q ∈ O, Pp q x := by
    intro x
    have hown : 2 * P.mP (own x) * max (|⟪P.g (own x), P.fM x⟫| - κ x * ‖P.fM x‖) 0 ^ 2 ≤
        Pp (own x) x := by
      refine positivePartForm_ge_of_oddInterference (E (own x)) (Ev (own x))
        (by linarith [hmP (own x)]) (P.g (own x)) (fun q => 2 * P.mP q)
        (fun q => by linarith [hmP q]) P.h (fun v => ?_) (hκ0 x) (hκ x) (P.fM x)
      rw [← hE (own x), ownerForm]
    have hsingle : Pp (own x) x ≤ ∑ q ∈ O, Pp q x :=
      Finset.single_le_sum (fun q _ => hPp0 q x) (hO x)
    have := hfree x
    nlinarith
  have hMsum : (O.card : ℝ) * ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) ≤ 2 * ∑ x, ∑ q ∈ O, Pp q x := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hcard : (0 : ℝ) < O.card := by exact_mod_cast hOne.card_pos
  have hHsum : ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) ≤ (Fintype.card ιH : ℝ) := by
    have : ∀ i, 2 * ‖P.fH i‖ ^ 2 - 1 ≤ 1 := fun i => by
      have := hH i; nlinarith [norm_nonneg (P.fH i)]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hfin : (O.card : ℝ) * A ≤ (O.card : ℝ) * ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) := by
    rw [hR, mul_add] at hsum
    linarith
  have := le_of_mul_le_mul_left hfin hcard
  linarith

end HorizontalPacket

end GaloisForLFunctions.HilbertMetric
