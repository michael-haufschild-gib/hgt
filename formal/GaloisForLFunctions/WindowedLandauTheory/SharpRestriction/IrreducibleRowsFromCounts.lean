import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.IrreducibleCountWeights
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.IrreducibleCountDominance
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.GlobalTheoremInputs
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.AutomorphicRowTie

/-! The bad-row count is bounded by the union of the two label
failures. Relative count estimates transfer the two local weights
to a bound for the fraction of bad rows. -/

noncomputable section

open Filter NumberField WindowedLandauTheory.MainNotions WindowedLandauTheory.BasicNotions
open WindowedLandauTheory.MainNotions.S WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace WindowedLandauTheory.ConcN

def DstarE {D : D7} (A : AllRows D) (e : A.B.I.Gf → ℂ) : ℝ :=
  A.B.I.Dstar (fdegAll A.B) A.B.μf A.B.fund e

def CountAllRows {D : D7} (A : AllRows D) (εC : ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ 0 < DstarE A A.B.e ∧
    ∀ (k : Fin 2) (S : Set (Tup D k)),
      |(A.dimT (cyl D k S) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤ εC * DstarE A (A.eT (cyl D k S))

def WeightAllRows {D : D7} (A : AllRows D) : Prop :=
  (∀ (k : Fin 2) v f, 0 ≤ wtOf D k (A.eVec k v) f) ∧
    ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) →
      locShare D A.eVec k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d

private theorem bad_share_of_counts {e d N b₁ b₂ p₁ p₂ W₁ W₂ b : ℝ}
    (he : 0 ≤ e) (he' : e < 1) (hd : 0 < d)
    (hN : |N - d| ≤ e * d) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hW₁ : p₁ ≤ W₁) (hW₂ : p₂ ≤ W₂)
    (hb₁ : |b₁ - p₁ * d| ≤ e * (p₁ * d)) (hb₂ : |b₂ - p₂ * d| ≤ e * (p₂ * d))
    (hb : b ≤ b₁ + b₂) :
    0 < N ∧ b / N ≤ (1 + e) / (1 - e) * (W₁ + W₂) := by
  have hden : 0 < 1 - e := sub_pos.mpr he'
  have hlow : (1 - e) * d ≤ N := by
    have h := (abs_le.mp hN).1
    linarith only [h]
  have hNp := (mul_pos hden hd).trans_le hlow
  have up₁ : b₁ ≤ (1 + e) * (p₁ * d) := by
    have h := (abs_le.mp hb₁).2
    linarith only [h]
  have up₂ : b₂ ≤ (1 + e) * (p₂ * d) := by
    have h := (abs_le.mp hb₂).2
    linarith only [h]
  have hm : (p₁ + p₂) * d ≤ (W₁ + W₂) * d :=
    mul_le_mul_of_nonneg_right (add_le_add hW₁ hW₂) hd.le
  have hr : 0 ≤ (1 + e) / (1 - e) * (W₁ + W₂) :=
    mul_nonneg (div_nonneg (add_nonneg zero_le_one he) hden.le)
      (add_nonneg (hp₁.trans hW₁) (hp₂.trans hW₂))
  refine ⟨hNp, (div_le_iff₀ hNp).mpr ?_⟩
  calc
    b ≤ b₁ + b₂ := hb
    _ ≤ (1 + e) * ((p₁ + p₂) * d) := by
      rw [add_mul p₁ p₂ d, mul_add]
      exact add_le_add up₁ up₂
    _ ≤ (1 + e) * ((W₁ + W₂) * d) := mul_le_mul_of_nonneg_left hm (add_nonneg zero_le_one he)
    _ = ((1 + e) / (1 - e) * (W₁ + W₂)) * ((1 - e) * d) := by field_simp [hden.ne']
    _ ≤ ((1 + e) / (1 - e) * (W₁ + W₂)) * N := mul_le_mul_of_nonneg_left hlow hr

theorem delp_of_allRows {D : D7} (A : AllRows D) (εC x ε : ℝ)
    (hT3 : LabelCountGoodInjective A) (hC : CountAllRows A εC) (hW : WeightAllRows A)
    (hnum : (1 + εC) / (1 - εC) *
      (Wg D.R.f D.R.m D.R.r (D.host.g 0) D.host.q D.host.d + Wg D.R.f D.R.m D.R.r (D.host.g 1) D.host.q D.host.d)
        ≤ Real.exp (-(x ^ (ε / 7)))) :
    Rows.DelpNonneg D.what₂ ∧ D.what₂.delp ≤ Real.exp (-(x ^ (ε / 7))) := by
  classical
  obtain ⟨hT3a, hinj, -, hgood⟩ := hT3
  obtain ⟨h0, hlt, hdSpos, hcount⟩ := hC
  obtain ⟨hwt, hW⟩ := hW
  set dS := DstarE A A.B.e with hdS

  have hDS : ∀ (k : Fin 2) (S : Finset (Tup D k)),
      DstarE A (A.eT (cyl D k (S : Set (Tup D k)))) = dS * locShare D A.eVec k S := by
    intro k S
    simp only [hdS, DstarE, AutInst.Dstar, locShare]
    rw [A.eT_one k S]
    ring

  have hdimU : A.dimT (cyl D 0 Set.univ) = D.what₂.Dall := by
    rw [hT3a]
    have hall : ∀ τ : Fin D.what₂.Dall, (fun k => A.labAll k τ) ∈ cyl D 0 Set.univ := fun τ => by simp [cyl]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card, Fintype.card_fin]
  have hU := hcount 0 Set.univ
  rw [hdimU, show cyl D 0 Set.univ = Set.univ from Set.eq_univ_of_forall fun _ => trivial,
    A.eT_univ] at hU

  let Sk : (k : Fin 2) → Finset (Tup D k) := fun k =>
    (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).image fun τ => A.labAll k τ
  have hSk : ∀ k, ∀ t ∈ Sk k, ¬ goodAt D k t := by
    intro k t ht
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hτ).2
  have hmem : ∀ (k : Fin 2) (τ : Fin D.what₂.Dall),
      (fun k => A.labAll k τ) ∈ cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k)) ↔
        ¬ goodAt D k (A.labAll k τ) := by
    intro k τ
    constructor
    · intro hτ; exact hSk k _ hτ
    · intro hτ
      show A.labAll k τ ∈ ((Sk k : Finset (Tup D k)) : Set (Tup D k))
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩, rfl⟩)
  have hdimK : ∀ k, A.dimT (cyl D k ((Sk k : Finset (Tup D k)) : Set (Tup D k))) =
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).card := by
    intro k
    rw [hT3a, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun τ => by rw [hmem k τ]; simp))

  have hDrows : (Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)).card =
      D.what₂.Drows := by
    have : (Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) =
        Finset.univ.image A.inc := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      rw [hgood τ]
      simp [Set.mem_range]
    rw [this, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle : D.what₂.Drows ≤ D.what₂.Dall := by
    rw [← hDrows]
    exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hbad : D.what₂.Dall ≤ D.what₂.Drows +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card := by
    have hsub : (Finset.univ : Finset (Fin D.what₂.Dall)) ⊆
        ((Finset.univ.filter fun τ : Fin D.what₂.Dall => D.ntypes.goodTuple (fun k => A.labAll k τ)) ∪
          (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ))) ∪
        (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)) := by
      intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hg : D.ntypes.goodTuple (fun k => A.labAll k τ)
      · exact Or.inl (Or.inl hg)
      · by_contra hc
        push Not at hc
        apply hg
        intro k
        fin_cases k
        · exact hc.1.2
        · exact hc.2
    have := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    rw [Finset.card_univ, Fintype.card_fin, hDrows] at this
    exact this

  have hloc : ∀ k, 0 ≤ locShare D A.eVec k (Sk k) := by
    intro k
    unfold locShare
    exact Finset.sum_nonneg (fun t _ => Finset.prod_nonneg (fun v _ => hwt k v (t v)))
  have hK : ∀ k, |((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D k (A.labAll k τ)).card : ℝ) -
      locShare D A.eVec k (Sk k) * dS| ≤ εC * (locShare D A.eVec k (Sk k) * dS) := by
    intro k
    have h := hcount k ((Sk k : Finset (Tup D k)) : Set (Tup D k))
    rw [hdimK k, hDS k (Sk k)] at h
    rwa [mul_comm dS] at h
  have hbadR : (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) ≤
      ((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card : ℝ) +
      ((Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card : ℝ) := by
    have : ((D.what₂.Dall : ℕ) : ℝ) ≤ ((D.what₂.Drows +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 0 (A.labAll 0 τ)).card +
      (Finset.univ.filter fun τ : Fin D.what₂.Dall => ¬ goodAt D 1 (A.labAll 1 τ)).card : ℕ) : ℝ) := by
      exact_mod_cast hbad
    push_cast at this
    linarith only [this]
  obtain ⟨hApos, hsh⟩ := bad_share_of_counts h0 hlt hdSpos hU
    (hloc 0) (hloc 1) (hW 0 (Sk 0) (hSk 0)) (hW 1 (Sk 1) (hSk 1))
    (hK 0) (hK 1) hbadR
  have hbE : (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) ≤ Real.exp (-(x ^ (ε / 7))) * (D.what₂.Dall : ℝ) := by
    have := hsh.trans hnum
    rwa [div_le_iff₀ hApos] at this
  have hdel : D.what₂.delp * (D.what₂.Dall : ℝ) = (D.what₂.Dall : ℝ) - (D.what₂.Drows : ℝ) := by
    rw [D.what₂.D_eq]
    ring
  have hle' : (D.what₂.Drows : ℝ) ≤ (D.what₂.Dall : ℝ) := by exact_mod_cast hle
  refine ⟨?_, ?_⟩
  · show 0 ≤ D.what₂.delp
    have hb : 0 ≤ D.what₂.delp * (D.what₂.Dall : ℝ) := by
      rw [hdel]
      exact sub_nonneg.mpr hle'
    exact nonneg_of_mul_nonneg_left hb hApos
  · have : D.what₂.delp * (D.what₂.Dall : ℝ) ≤ Real.exp (-(x ^ (ε / 7))) * (D.what₂.Dall : ℝ) := by rw [hdel]; exact hbE
    exact le_of_mul_le_mul_right this hApos

theorem linkIRR_of_allRows (eps Cs c : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) (hc : 0 < c)
    (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧ CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
      WeightAllRows A ∧ SizesRec (Fm.D x i) x Fm.ez Cs) :
    LinkIRR Fm := by
  obtain ⟨x0, hx0⟩ := h
  have hez : 0 < Fm.ez := div_pos he (zero_lt_one.trans_le Fm.one_le_J)
  have hez1 : Fm.ez ≤ 1 := (div_le_self he.le Fm.one_le_J).trans he1
  have hev := (eventually_weight_distortion_le (3 * Cs + 3) Fm.ez hez).and
    ((weight_numbers_bound Fm.ez Cs hez hez1).and (epsilon_bound_large_x c hc))
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max x0 x1, fun x hx i => ?_⟩
  obtain ⟨A, hT, hC, hW, hS⟩ := hx0 x ((le_max_left _ _).trans hx) i
  obtain ⟨hnum, hw, heps⟩ := hx1 x ((le_max_right _ _).trans hx)
  exact delp_of_allRows A _ x Fm.ez hT hC hW
    (hnum _ _ _ (Real.exp_pos _).le (heps _ _ (hS 0).2.2.2.2.1 (hS 0).2.1)
      (hw _ _ _ _ _ _ (hS 0)) (hw _ _ _ _ _ _ (hS 1)))

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.linkIRR_of_allRows
