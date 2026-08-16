import GaloisForLFunctions.HTGeometry.TwoSiteLabelProduct
import GaloisForLFunctions.HTGeometry.FieldRigidCoupling

/-!
# The two-site relation of a commuting chain shell operator

Pairing the commutator of an open-chain two-local operator with a purely one-site operator against
a Pauli string supported on the two sites of an edge leaves only that edge and its two endpoints,
and the resulting scalar equation is exactly the vanishing of the local-field commutator map of
that edge coupling.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Support

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Two one-site labels never contribute to a two-site string. -/
theorem pairCoeff2_eq_zero_of_card_one_card_one {ι κ : Type*} (S : ι → (σ → Option (Fin 3)))
    (T : κ → (σ → Option (Fin 3))) (h : ι → ℂ) (k : κ → ℂ) (R : σ → Option (Fin 3))
    (hR : (labelSupport R).card = 2) {i : ι} {j : κ}
    (hSi : (labelSupport (S i)).card = 1) (hTj : (labelSupport (T j)).card = 1) :
    pairCoeff2 S T h k R i j = 0 := by
  classical
  by_cases hdisj : Disjoint (labelSupport (S i)) (labelSupport (T j))
  · rw [pairCoeff2, optPhaseProd_sub_eq_zero_of_disjoint hdisj, zero_mul, mul_zero]
  · by_cases hRij : R = optMulLabel (S i) (T j)
    · exfalso
      obtain ⟨s, hs⟩ := Finset.not_disjoint_iff.mp hdisj
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hSi
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hTj
      rw [hu, Finset.mem_singleton] at hs
      rw [ht, Finset.mem_singleton] at hs
      have hut : u = t := hs.1.symm.trans hs.2
      have hsub : labelSupport R ⊆ labelSupport (S i) := by
        rw [hRij]
        refine (labelSupport_optMulLabel_subset _ _).trans ?_
        rw [hu, ht, hut]
        exact Finset.union_subset subset_rfl subset_rfl
      have := Finset.card_le_card hsub
      omega
    · rw [pairCoeff2, if_neg hRij, mul_zero, mul_zero]

/-- A two-site factor whose support is not the string's support never contributes. -/
theorem pairCoeff2_eq_zero_of_support_ne {ι κ : Type*} (S : ι → (σ → Option (Fin 3)))
    (T : κ → (σ → Option (Fin 3))) (h : ι → ℂ) (k : κ → ℂ) (R : σ → Option (Fin 3))
    (hR : (labelSupport R).card = 2) {i : ι} {j : κ}
    (hSi : (labelSupport (S i)).card = 2) (hTj : (labelSupport (T j)).card = 1)
    (hne : labelSupport (S i) ≠ labelSupport R) :
    pairCoeff2 S T h k R i j = 0 := by
  classical
  by_cases hRij : R = optMulLabel (S i) (T j)
  · exfalso
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hTj
    by_cases hmem : s ∈ labelSupport (S i)
    · have hsub : labelSupport R ⊆ labelSupport (S i) := by
        rw [hRij]
        refine (labelSupport_optMulLabel_subset _ _).trans ?_
        rw [hs]
        refine Finset.union_subset (le_refl _) ?_
        intro t ht
        rw [Finset.mem_singleton] at ht
        exact ht ▸ hmem
      exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    · have h1 : labelSupport (S i) ⊆ labelSupport R := by
        intro t ht
        rw [hRij]
        refine mem_labelSupport_optMulLabel_of_left (mem_labelSupport.mp ht) ?_
        by_contra hc
        have hts : t ∈ labelSupport (T j) := mem_labelSupport.mpr hc
        rw [hs, Finset.mem_singleton] at hts
        exact hmem (hts ▸ ht)
      have h2 : s ∈ labelSupport R := by
        rw [hRij]
        refine mem_labelSupport_optMulLabel_of_right ?_ ?_
        · by_contra hc
          exact hmem (mem_labelSupport.mpr hc)
        · exact mem_labelSupport.mp (by rw [hs]; exact Finset.mem_singleton_self s)
      have hins : insert s (labelSupport (S i)) ⊆ labelSupport R := Finset.insert_subset h2 h1
      have hcard : (insert s (labelSupport (S i))).card = 3 := by
        rw [Finset.card_insert_of_notMem hmem, hSi]
      have := Finset.card_le_card hins
      omega
  · rw [pairCoeff2, if_neg hRij, mul_zero, mul_zero]

/-- A one-site factor outside the string's support never contributes. -/
theorem pairCoeff2_eq_zero_of_site_notMem {ι κ : Type*} (S : ι → (σ → Option (Fin 3)))
    (T : κ → (σ → Option (Fin 3))) (h : ι → ℂ) (k : κ → ℂ) (R : σ → Option (Fin 3))
    {i : ι} {j : κ} {s : σ} (hSi : labelSupport (S i) = labelSupport R)
    (hTj : labelSupport (T j) = {s}) (hs : s ∉ labelSupport R) :
    pairCoeff2 S T h k R i j = 0 := by
  classical
  by_cases hRij : R = optMulLabel (S i) (T j)
  · exfalso
    refine hs ?_
    rw [hRij]
    refine mem_labelSupport_optMulLabel_of_right ?_ ?_
    · by_contra hc
      exact hs (hSi ▸ mem_labelSupport.mpr hc)
    · exact mem_labelSupport.mp (by rw [hTj]; exact Finset.mem_singleton_self s)
  · rw [pairCoeff2, if_neg hRij, mul_zero, mul_zero]

end Support

section Chain

variable {m : ℕ}

theorem chainSites_injective {p p' : Fin m} (h : chainSites p = chainSites p') : p = p' := by
  have h1 : (p.castSucc : Fin (m + 1)) ∈ chainSites p' := by
    rw [← h, chainSites]
    exact Finset.mem_insert_self _ _
  have h2 : (p'.castSucc : Fin (m + 1)) ∈ chainSites p := by
    rw [h, chainSites]
    exact Finset.mem_insert_self _ _
  rw [mem_chainSites, Fin.val_castSucc] at h1 h2
  exact Fin.ext (by omega)

theorem labelSupport_chainSiteLabel_eq (s : Fin (m + 1)) (c : Fin 3) :
    labelSupport (chainSiteLabel ((s, c) : Fin (m + 1) × Fin 3)) = {s} :=
  labelSupport_siteLabel s c

theorem labelSupport_chainPairLabel (p : Fin m) (f q : Fin 3) :
    labelSupport (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) = chainSites p := by
  rw [labelSupport_pairLabel (castSucc_ne_succ p), chainSites]

theorem card_labelSupport_chainPairLabel (p : Fin m) (f q : Fin 3) :
    (labelSupport (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q)).card = 2 := by
  rw [labelSupport_chainPairLabel, card_chainSites]

end Chain

section SumHelpers

theorem sum_three_ite_mid (q : Fin 3) (W : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (if b = q then (1 : ℂ) else 0) * W a b c)
      = ∑ a : Fin 3, ∑ c : Fin 3, W a q c := by
  classical
  refine Finset.sum_congr rfl fun a _ => ?_
  have hb : ∀ b : Fin 3, (∑ c : Fin 3, (if b = q then (1 : ℂ) else 0) * W a b c) =
      (if b = q then (1 : ℂ) else 0) * ∑ c : Fin 3, W a b c := by
    intro b
    rw [Finset.mul_sum]
  simp only [hb]
  simp

theorem sum_three_ite_out (f : Fin 3) (W : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (if a = f then (1 : ℂ) else 0) * W a b c)
      = ∑ b : Fin 3, ∑ c : Fin 3, W f b c := by
  classical
  have ha : ∀ a : Fin 3, (∑ b : Fin 3, ∑ c : Fin 3, (if a = f then (1 : ℂ) else 0) * W a b c) =
      (if a = f then (1 : ℂ) else 0) * ∑ b : Fin 3, ∑ c : Fin 3, W a b c := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
  simp only [ha]
  simp

end SumHelpers


section Blocks

variable {m : ℕ}

/-- The commutator coefficient of a two-site term against a one-site term. -/
def chainSiteEdgeTerm (J : Fin m → Fin 3 → Fin 3 → ℝ) (k : Fin (m + 1) → Fin 3 → ℝ)
    (R : Fin (m + 1) → Option (Fin 3)) (q1 : Fin m × Fin 3 × Fin 3)
    (q2 : Fin (m + 1) × Fin 3) : ℂ :=
  pairCoeff2 chainEdgeLabel chainSiteLabel (chainEdgeCoeff J) (chainSiteCoeff k) R q1 q2

/-- The total commutator coefficient of an edge against a site. -/
def chainEdgeSiteBlock (J : Fin m → Fin 3 → Fin 3 → ℝ) (k : Fin (m + 1) → Fin 3 → ℝ)
    (R : Fin (m + 1) → Option (Fin 3)) (p : Fin m) (s : Fin (m + 1)) : ℂ :=
  ∑ u : Fin 3 × Fin 3, ∑ c : Fin 3, chainSiteEdgeTerm J k R (p, u) (s, c)

/-- **The commutator equation at a two-site string involves only edge–site pairs.** -/
theorem sum_chainSiteEdgeTerm_eq_zero (h1 k : Fin (m + 1) → Fin 3 → ℝ)
    (J : Fin m → Fin 3 → Fin 3 → ℝ)
    (hcomm : (chainSiteOp h1 + chainEdgeOp J) * chainSiteOp k =
      chainSiteOp k * (chainSiteOp h1 + chainEdgeOp J))
    (R : Fin (m + 1) → Option (Fin 3)) (hR : (labelSupport R).card = 2) :
    (∑ q1, ∑ q2, chainSiteEdgeTerm J k R q1 q2) = 0 := by
  classical
  have hzero : (chainSiteOp h1 + chainEdgeOp J) * chainSiteOp k -
      chainSiteOp k * (chainSiteOp h1 + chainEdgeOp J) = 0 := sub_eq_zero_of_eq hcomm
  have hexp : (chainSiteOp h1 + chainEdgeOp J) * chainSiteOp k -
      chainSiteOp k * (chainSiteOp h1 + chainEdgeOp J) =
      (chainSiteOp h1 * chainSiteOp k - chainSiteOp k * chainSiteOp h1) +
      (chainEdgeOp J * chainSiteOp k - chainSiteOp k * chainEdgeOp J) := by
    noncomm_ring
  have htr : Matrix.trace (finitePauliMatrix R *
      ((chainSiteOp h1 * chainSiteOp k - chainSiteOp k * chainSiteOp h1) +
      (chainEdgeOp J * chainSiteOp k - chainSiteOp k * chainEdgeOp J))) = 0 := by
    rw [← hexp, hzero, Matrix.mul_zero, Matrix.trace_zero]
  rw [Matrix.mul_add, Matrix.trace_add, chainSiteOp_eq h1, chainSiteOp_eq k, chainEdgeOp_eq J,
    trace_commutator_eq_smul_sum, trace_commutator_eq_smul_sum] at htr
  have hs1 : (∑ i, ∑ j, pairCoeff2 chainSiteLabel chainSiteLabel (chainSiteCoeff h1)
      (chainSiteCoeff k) R i j) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      pairCoeff2_eq_zero_of_card_one_card_one _ _ _ _ _ hR (card_labelSupport_chainSiteLabel i)
        (card_labelSupport_chainSiteLabel j)
  rw [hs1] at htr
  simp only [mul_zero, zero_add] at htr
  exact (mul_eq_zero.mp htr).resolve_left (pow_ne_zero _ two_ne_zero)

theorem sum_chainEdgeSiteBlock_eq_zero (h1 k : Fin (m + 1) → Fin 3 → ℝ)
    (J : Fin m → Fin 3 → Fin 3 → ℝ)
    (hcomm : (chainSiteOp h1 + chainEdgeOp J) * chainSiteOp k =
      chainSiteOp k * (chainSiteOp h1 + chainEdgeOp J))
    (R : Fin (m + 1) → Option (Fin 3)) (hR : (labelSupport R).card = 2) :
    (∑ p, ∑ s, chainEdgeSiteBlock J k R p s) = 0 := by
  classical
  have h := sum_chainSiteEdgeTerm_eq_zero h1 k J hcomm R hR
  rw [Fintype.sum_prod_type (fun q1 => ∑ q2, chainSiteEdgeTerm J k R q1 q2)] at h
  rw [show (∑ p, ∑ u : Fin 3 × Fin 3, ∑ q2, chainSiteEdgeTerm J k R (p, u) q2) =
      ∑ p, ∑ u : Fin 3 × Fin 3, ∑ s, ∑ c : Fin 3,
        chainSiteEdgeTerm J k R (p, u) (s, c) from
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun u _ =>
      Fintype.sum_prod_type (fun q2 => chainSiteEdgeTerm J k R (p, u) q2)] at h
  rw [show (∑ p, ∑ u : Fin 3 × Fin 3, ∑ s, ∑ c : Fin 3, chainSiteEdgeTerm J k R (p, u) (s, c)) =
      ∑ p, ∑ s, chainEdgeSiteBlock J k R p s from
    Finset.sum_congr rfl fun p _ => Finset.sum_comm] at h
  exact h

/-- The edge–site coefficient at the left endpoint. -/
theorem chainEdgeSiteBlock_left (J : Fin m → Fin 3 → Fin 3 → ℝ)
    (k : Fin (m + 1) → Fin 3 → ℝ) (p : Fin m) (f q : Fin 3) :
    chainEdgeSiteBlock J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p p.castSucc =
      2 * Complex.I *
        ((crossProduct (fun a => J p a q) (fun c => k p.castSucc c) f : ℝ) : ℂ) := by
  classical
  have hvw := castSucc_ne_succ p
  have hind : ∀ a b c : Fin 3,
      (if pairLabel (p.castSucc : Fin (m + 1)) p.succ f q =
          optMulLabel (chainEdgeLabel ((p, a, b) : Fin m × Fin 3 × Fin 3))
            (chainSiteLabel ((p.castSucc, c) : Fin (m + 1) × Fin 3)) then (1 : ℂ) else 0) =
      (if b = q then (1 : ℂ) else 0) *
        (if some f = optMul (some a) (some c) then (1 : ℂ) else 0) := by
    intro a b c
    by_cases h1 : b = q <;> by_cases h2 : (some f : Option (Fin 3)) = optMul (some a) (some c) <;>
      simp [chainEdgeLabel, chainSiteLabel, pairLabel_eq_optMulLabel_left_iff hvw, h1, h2]
  have hph1 : ∀ a b c : Fin 3,
      optPhaseProd (chainEdgeLabel ((p, a, b) : Fin m × Fin 3 × Fin 3))
        (chainSiteLabel ((p.castSucc, c) : Fin (m + 1) × Fin 3)) =
        optPhase (some a) (some c) := fun a b c =>
    optPhaseProd_pairLabel_siteLabel_left a b c
  have hph2 : ∀ a b c : Fin 3,
      optPhaseProd (chainSiteLabel ((p.castSucc, c) : Fin (m + 1) × Fin 3))
        (chainEdgeLabel ((p, a, b) : Fin m × Fin 3 × Fin 3)) =
        optPhase (some c) (some a) := fun a b c =>
    optPhaseProd_siteLabel_pairLabel_left a b c
  have hterm : ∀ a b c : Fin 3,
      chainSiteEdgeTerm J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) (p, a, b)
          (p.castSucc, c) =
        (if b = q then (1 : ℂ) else 0) *
          (((J p a b : ℝ) : ℂ) * ((k p.castSucc c : ℝ) : ℂ) * (pauliComm a c *
            (if some f = optMul (some a) (some c) then (1 : ℂ) else 0))) := by
    intro a b c
    simp only [chainSiteEdgeTerm, pairCoeff2, chainEdgeCoeff, chainSiteCoeff, pauliComm,
      hph1, hph2, hind]
    ring
  have hexpand : chainEdgeSiteBlock J k
      (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p p.castSucc =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        chainSiteEdgeTerm J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) (p, a, b)
          (p.castSucc, c) := by
    rw [chainEdgeSiteBlock, Fintype.sum_prod_type]
  rw [hexpand]
  simp only [hterm]
  rw [sum_three_ite_mid q fun a b c => ((J p a b : ℝ) : ℂ) * ((k p.castSucc c : ℝ) : ℂ) *
    (pauliComm a c * (if some f = optMul (some a) (some c) then (1 : ℂ) else 0))]
  exact sum_pauliComm_eq_cross (fun a => J p a q) (fun c => k p.castSucc c) f

/-- The edge–site coefficient at the right endpoint. -/
theorem chainEdgeSiteBlock_right (J : Fin m → Fin 3 → Fin 3 → ℝ)
    (k : Fin (m + 1) → Fin 3 → ℝ) (p : Fin m) (f q : Fin 3) :
    chainEdgeSiteBlock J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p p.succ =
      2 * Complex.I * ((crossProduct (fun b => J p f b) (fun c => k p.succ c) q : ℝ) : ℂ) := by
  classical
  have hvw := castSucc_ne_succ p
  have hind : ∀ a b c : Fin 3,
      (if pairLabel (p.castSucc : Fin (m + 1)) p.succ f q =
          optMulLabel (chainEdgeLabel ((p, a, b) : Fin m × Fin 3 × Fin 3))
            (chainSiteLabel ((p.succ, c) : Fin (m + 1) × Fin 3)) then (1 : ℂ) else 0) =
      (if a = f then (1 : ℂ) else 0) *
        (if some q = optMul (some b) (some c) then (1 : ℂ) else 0) := by
    intro a b c
    by_cases h1 : a = f <;> by_cases h2 : (some q : Option (Fin 3)) = optMul (some b) (some c) <;>
      simp [chainEdgeLabel, chainSiteLabel, pairLabel_eq_optMulLabel_right_iff hvw, h1, h2]
  have hph1 : ∀ a b c : Fin 3,
      optPhaseProd (chainEdgeLabel ((p, a, b) : Fin m × Fin 3 × Fin 3))
        (chainSiteLabel ((p.succ, c) : Fin (m + 1) × Fin 3)) =
        optPhase (some b) (some c) := fun a b c =>
    optPhaseProd_pairLabel_siteLabel_right hvw a b c
  have hph2 : ∀ a b c : Fin 3,
      optPhaseProd (chainSiteLabel ((p.succ, c) : Fin (m + 1) × Fin 3))
        (chainEdgeLabel ((p, a, b) : Fin m × Fin 3 × Fin 3)) =
        optPhase (some c) (some b) := fun a b c =>
    optPhaseProd_siteLabel_pairLabel_right hvw a b c
  have hterm : ∀ a b c : Fin 3,
      chainSiteEdgeTerm J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) (p, a, b)
          (p.succ, c) =
        (if a = f then (1 : ℂ) else 0) *
          (((J p a b : ℝ) : ℂ) * ((k p.succ c : ℝ) : ℂ) * (pauliComm b c *
            (if some q = optMul (some b) (some c) then (1 : ℂ) else 0))) := by
    intro a b c
    simp only [chainSiteEdgeTerm, pairCoeff2, chainEdgeCoeff, chainSiteCoeff, pauliComm,
      hph1, hph2, hind]
    ring
  have hexpand : chainEdgeSiteBlock J k
      (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p p.succ =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        chainSiteEdgeTerm J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) (p, a, b)
          (p.succ, c) := by
    rw [chainEdgeSiteBlock, Fintype.sum_prod_type]
  rw [hexpand]
  simp only [hterm]
  rw [sum_three_ite_out f fun a b c => ((J p a b : ℝ) : ℂ) * ((k p.succ c : ℝ) : ℂ) *
    (pauliComm b c * (if some q = optMul (some b) (some c) then (1 : ℂ) else 0))]
  exact sum_pauliComm_eq_cross (fun b => J p f b) (fun c => k p.succ c) q


/-- **The local-field commutator map of every edge vanishes.**

If an open-chain two-local operator commutes with a purely one-site operator, then at every edge
the local-field commutator map of the edge coupling annihilates the pair of one-site fields at the
edge's endpoints. -/
theorem fieldMap_eq_zero_of_commute (h1 k : Fin (m + 1) → Fin 3 → ℝ)
    (J : Fin m → Fin 3 → Fin 3 → ℝ)
    (hcomm : (chainSiteOp h1 + chainEdgeOp J) * chainSiteOp k =
      chainSiteOp k * (chainSiteOp h1 + chainEdgeOp J))
    (p : Fin m) :
    fieldMap (J p) (fun a => k p.castSucc a) (fun b => k p.succ b) = 0 := by
  classical
  refine Matrix.ext fun f q => ?_
  rw [Matrix.zero_apply]
  have hvw := castSucc_ne_succ p
  have htot := sum_chainEdgeSiteBlock_eq_zero h1 k J hcomm
    (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) (card_labelSupport_chainPairLabel p f q)
  have hblk_ne : ∀ p' : Fin m, p' ≠ p → ∀ s : Fin (m + 1),
      chainEdgeSiteBlock J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p' s = 0 := by
    intro p' hp' s
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun c _ => ?_
    refine pairCoeff2_eq_zero_of_support_ne _ _ _ _ _ (card_labelSupport_chainPairLabel p f q)
      (card_labelSupport_chainEdgeLabel _) (card_labelSupport_chainSiteLabel _) ?_
    rw [labelSupport_chainEdgeLabel, labelSupport_chainPairLabel]
    exact fun hc => hp' (chainSites_injective hc)
  have hblk_site : ∀ s : Fin (m + 1), s ≠ p.castSucc → s ≠ p.succ →
      chainEdgeSiteBlock J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p s = 0 := by
    intro s hs1 hs2
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun c _ => ?_
    refine pairCoeff2_eq_zero_of_site_notMem _ _ _ _ _ ?_ (labelSupport_chainSiteLabel_eq s c) ?_
    · rw [labelSupport_chainEdgeLabel, labelSupport_chainPairLabel]
    · rw [labelSupport_chainPairLabel, chainSites, Finset.mem_insert, Finset.mem_singleton]
      exact fun hc => hc.elim hs1 hs2
  have hrow : (∑ s, chainEdgeSiteBlock J k
      (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p s) =
      chainEdgeSiteBlock J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p p.castSucc +
      chainEdgeSiteBlock J k (pairLabel (p.castSucc : Fin (m + 1)) p.succ f q) p p.succ :=
    Finset.sum_eq_add_of_mem _ _ (Finset.mem_univ _) (Finset.mem_univ _) hvw
      (fun c _ hc => hblk_site c hc.1 hc.2)
  rw [Finset.sum_eq_single p (fun p' _ hp' => Finset.sum_eq_zero fun s _ => hblk_ne p' hp' s)
    (fun hc => absurd (Finset.mem_univ p) hc), hrow, chainEdgeSiteBlock_left,
    chainEdgeSiteBlock_right] at htot
  have hfm : ((fieldMap (J p) (fun a => k p.castSucc a) (fun b => k p.succ b) f q : ℝ) : ℂ) = 0 := by
    have h2 : (2 * Complex.I) *
        ((fieldMap (J p) (fun a => k p.castSucc a) (fun b => k p.succ b) f q : ℝ) : ℂ) = 0 := by
      simp only [fieldMap]
      push_cast
      linear_combination htot
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  exact Complex.ofReal_eq_zero.mp hfm

end Blocks

end GaloisForLFunctions.HTGeometry
