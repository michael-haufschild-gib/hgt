import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport
import GaloisForLFunctions.HTGeometry.ProductStabilizerPhysicalScore

/-!
# Operator-norm probes for alternating path bonds

A global sign flip removes onsite terms. An alternating flip of paired
sites then removes bonds between pairs. The four product-state probes
recover the sum of magnitudes of one chosen Pauli direction on the pairs.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

private abbrev PathMatrix (n : ℕ) :=
  Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ

private abbrev PathProbe (n : ℕ) := Fin (n + 2) → Fin 3 × Bool

private def probePairing (p : PathProbe n) : PathMatrix n →ₗ[ℂ] ℂ where
  toFun H := (productStabilizerDensity p * H).trace
  map_add' X Y := by rw [Matrix.mul_add, Matrix.trace_add]
  map_smul' a X := by rw [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply]

private theorem norm_probePairing_le (p : PathProbe n) (H : PathMatrix n) :
    ‖probePairing p H‖ ≤ ‖H‖ := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (productStabilizerDensity p)
  rw [productStabilizerDensity_isHermitian p, productStabilizerDensity_mul_self p] at h
  exact norm_trace_densityMatrix_mul_le h (trace_productStabilizerDensity p) H

private def probeFlip (p : PathProbe n) (f : Fin (n + 2) → Bool) : PathProbe n :=
  fun s => ((p s).1, if f s then !(p s).2 else (p s).2)

private theorem probeFactor_flip (p : PathProbe n) (f : Fin (n + 2) → Bool)
    (s : Fin (n + 2)) (a : Fin 3) :
    stabilizerAxisExpectation (probeFlip p f s) (some a) =
      if f s then -stabilizerAxisExpectation (p s) (some a) else stabilizerAxisExpectation (p s) (some a) := by
  cases hf : f s <;> cases hs : (p s).2 <;> by_cases ha : (p s).1 = a <;>
    simp [probeFlip, stabilizerAxisExpectation, hf, hs, ha]

private theorem probePairing_onsite (p : PathProbe n) (s : Fin (n + 2)) (a : Fin 3) :
    probePairing p (finitePauliMatrix (onsiteWord s a)) =
      (stabilizerAxisExpectation (p s) (some a) : ℂ) := by
  change (productStabilizerDensity p * finitePauliMatrix (onsiteWord s a)).trace = _
  rw [trace_productStabilizerDensity_mul_finitePauliMatrix]
  congr 1
  calc
    (∏ t, stabilizerAxisExpectation (p t) (onsiteWord s a t)) =
        ∏ t, if t = s then stabilizerAxisExpectation (p t) (some a) else 1 := by
      exact Finset.prod_congr rfl fun t _ => by
        by_cases h : t = s <;> simp [onsiteWord, h, stabilizerAxisExpectation]
    _ = _ := Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ _)

private theorem probePairing_bond (p : PathProbe n) (e : Fin (n + 1)) (a : Fin 3 × Fin 3) :
    probePairing p (finitePauliMatrix (couplingWord e a)) =
      ((stabilizerAxisExpectation (p e.castSucc) (some a.1) *
        stabilizerAxisExpectation (p e.succ) (some a.2) : ℝ) : ℂ) := by
  change (productStabilizerDensity p * finitePauliMatrix (couplingWord e a)).trace = _
  rw [trace_productStabilizerDensity_mul_finitePauliMatrix]
  congr 1
  have he : e.castSucc ≠ e.succ := by
    intro h
    have hv := congrArg Fin.val h
    change e.val = e.val + 1 at hv
    omega
  calc
    (∏ t, stabilizerAxisExpectation (p t) (couplingWord e a t)) =
        ∏ t, (if t = e.castSucc then stabilizerAxisExpectation (p t) (some a.1) else 1) *
          (if t = e.succ then stabilizerAxisExpectation (p t) (some a.2) else 1) := by
      apply Finset.prod_congr rfl
      intro t _
      by_cases h₁ : t = e.castSucc
      · subst t
        simp [couplingWord, he]
      · by_cases h₂ : t = e.succ
        · subst t
          simp [couplingWord, Ne.symm he]
        · simp [couplingWord, h₁, h₂, stabilizerAxisExpectation]
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ _),
        Finset.prod_ite_eq_of_mem' _ _ _ (Finset.mem_univ _)]

private def evenProbe (p : PathProbe n) : PathMatrix n →ₗ[ℂ] ℂ :=
  probePairing p + probePairing (probeFlip p (fun _ => true))

private theorem norm_evenProbe_le (p : PathProbe n) (H : PathMatrix n) :
    ‖evenProbe p H‖ ≤ 2 * ‖H‖ := by
  change ‖probePairing p H + probePairing (probeFlip p (fun _ => true)) H‖ ≤ _
  rw [two_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_probePairing_le _ _) (norm_probePairing_le _ _))

private theorem evenProbe_onsite (p : PathProbe n) (s : Fin (n + 2)) (a : Fin 3) :
    evenProbe p (finitePauliMatrix (onsiteWord s a)) = 0 := by
  simp only [evenProbe, LinearMap.add_apply, probePairing_onsite, probeFactor_flip, if_true,
    Complex.ofReal_neg, add_neg_cancel]

private theorem evenProbe_bond (p : PathProbe n) (e : Fin (n + 1)) (a : Fin 3 × Fin 3) :
    evenProbe p (finitePauliMatrix (couplingWord e a)) =
      2 * ((stabilizerAxisExpectation (p e.castSucc) (some a.1) *
        stabilizerAxisExpectation (p e.succ) (some a.2) : ℝ) : ℂ) := by
  simp only [evenProbe, LinearMap.add_apply, probePairing_bond, probeFactor_flip, if_true,
    neg_mul_neg, two_mul]

private def pairFlip (r : Fin 2) (s : Fin (n + 2)) : Bool :=
  decide (((s.val + r.val) / 2) % 2 = 1)

private theorem pairFlip_eq_iff (r : Fin 2) (e : Fin (n + 1)) :
    pairFlip r e.castSucc = pairFlip r e.succ ↔ (e.val + r.val) % 2 = 0 := by
  unfold pairFlip
  change (decide (((e.val + r.val) / 2) % 2 = 1) =
    decide (((e.val + 1 + r.val) / 2) % 2 = 1)) ↔ _
  by_cases he : (e.val + r.val) % 2 = 0
  · have h : (e.val + r.val) / 2 = (e.val + 1 + r.val) / 2 := by omega
    simp [he, h]
  · have h : (e.val + 1 + r.val) / 2 = (e.val + r.val) / 2 + 1 := by omega
    have h₀ : ((e.val + r.val) / 2 + 1) % 2 = 1 ↔
        ¬ ((e.val + r.val) / 2) % 2 = 1 := by omega
    by_cases hp : ((e.val + r.val) / 2) % 2 = 1 <;> simp [h, h₀, hp, he]

private def alternatingProbe (p : PathProbe n) (r : Fin 2) : PathMatrix n →ₗ[ℂ] ℂ :=
  evenProbe p + evenProbe (probeFlip p (pairFlip r))

private theorem norm_alternatingProbe_le (p : PathProbe n) (r : Fin 2) (H : PathMatrix n) :
    ‖alternatingProbe p r H‖ ≤ 4 * ‖H‖ := by
  change ‖evenProbe p H + evenProbe (probeFlip p (pairFlip r)) H‖ ≤ _
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ 2 * ‖H‖ + 2 * ‖H‖ := add_le_add (norm_evenProbe_le _ _) (norm_evenProbe_le _ _)
    _ = _ := by ring

private theorem alternatingProbe_onsite (p : PathProbe n) (r : Fin 2) (s : Fin (n + 2)) (a : Fin 3) :
    alternatingProbe p r (finitePauliMatrix (onsiteWord s a)) = 0 := by
  simp only [alternatingProbe, LinearMap.add_apply, evenProbe_onsite, add_zero]

private theorem alternatingProbe_bond (p : PathProbe n) (r : Fin 2)
    (e : Fin (n + 1)) (a : Fin 3 × Fin 3) :
    alternatingProbe p r (finitePauliMatrix (couplingWord e a)) =
      if (e.val + r.val) % 2 = 0 then
        4 * ((stabilizerAxisExpectation (p e.castSucc) (some a.1) *
          stabilizerAxisExpectation (p e.succ) (some a.2) : ℝ) : ℂ)
      else 0 := by
  simp only [alternatingProbe, LinearMap.add_apply, evenProbe_bond, probeFactor_flip,
    ← pairFlip_eq_iff r e]
  cases pairFlip r e.castSucc <;> cases pairFlip r e.succ <;> simp <;> ring

private def alignedBondProbe (u : PathShell n) (r : Fin 2) (a : Fin 3 × Fin 3) : PathProbe n :=
  fun s => if (s.val + r.val) % 2 = 0 then (a.1, true)
    else if hs : s.val = 0 then (a.2, true)
    else (a.2, decide (0 ≤ u (.inr (⟨s.val - 1, by have := s.isLt; omega⟩, a))))

private theorem alignedBondProbe_left (u : PathShell n) (r : Fin 2) (a : Fin 3 × Fin 3)
    (e : Fin (n + 1)) (he : (e.val + r.val) % 2 = 0) :
    alignedBondProbe u r a e.castSucc = (a.1, true) :=
  if_pos he

private theorem alignedBondProbe_right (u : PathShell n) (r : Fin 2) (a : Fin 3 × Fin 3)
    (e : Fin (n + 1)) (he : (e.val + r.val) % 2 = 0) :
    alignedBondProbe u r a e.succ = (a.2, decide (0 ≤ u (.inr (e, a)))) := by
  have h : ¬ (e.val + 1 + r.val) % 2 = 0 := by omega
  unfold alignedBondProbe
  simp only [Fin.val_succ, h, Nat.succ_ne_zero, dite_false]
  rfl

private theorem alignedBondProbe_value (u : PathShell n) (r : Fin 2) (a b : Fin 3 × Fin 3)
    (e : Fin (n + 1)) (he : (e.val + r.val) % 2 = 0) :
    u (.inr (e, b)) * (stabilizerAxisExpectation (alignedBondProbe u r a e.castSucc) (some b.1) *
      stabilizerAxisExpectation (alignedBondProbe u r a e.succ) (some b.2)) =
    if b = a then |u (.inr (e, a))| else 0 := by
  rw [alignedBondProbe_left u r a e he, alignedBondProbe_right u r a e he]
  by_cases h₁ : a.1 = b.1
  · by_cases h₂ : a.2 = b.2
    · have hb : b = a := Prod.ext h₁.symm h₂.symm
      subst b
      by_cases h : 0 ≤ u (.inr (e, a))
      · simp [stabilizerAxisExpectation, h, abs_of_nonneg h]
      · simp [stabilizerAxisExpectation, h, abs_of_neg (lt_of_not_ge h)]
    · have hb : b ≠ a := fun h => h₂ (congrArg Prod.snd h).symm
      simp [stabilizerAxisExpectation, h₁, h₂, hb]
  · have hb : b ≠ a := fun h => h₁ (congrArg Prod.fst h).symm
    simp [stabilizerAxisExpectation, h₁, hb]

/-- For either parity, the sum of absolute coefficients of a prescribed
Pauli direction on that parity of bonds is below the operator norm. -/
theorem alternating_bond_abs_sum_le_pathHamiltonian_norm (u : PathShell n)
    (r : Fin 2) (a : Fin 3 × Fin 3) :
    (∑ e : Fin (n + 1), if (e.val + r.val) % 2 = 0 then |u (.inr (e, a))| else 0) ≤
      ‖pathHamiltonian u‖ := by
  classical
  let p := alignedBondProbe u r a
  let L := alternatingProbe p r
  let S := ∑ e : Fin (n + 1), if (e.val + r.val) % 2 = 0 then |u (.inr (e, a))| else 0
  have hS : 0 ≤ S := Finset.sum_nonneg fun e _ => by
    split <;> simp only [abs_nonneg, le_refl]
  have hsingle (e : Fin (n + 1)) (b : Fin 3 × Fin 3) :
      (u (.inr (e, b)) : ℂ) * L (finitePauliMatrix (couplingWord e b)) =
        if (e.val + r.val) % 2 = 0 then if b = a then 4 * ((|u (.inr (e, a))| : ℝ) : ℂ) else 0 else 0 := by
    unfold L
    rw [alternatingProbe_bond]
    by_cases he : (e.val + r.val) % 2 = 0
    · rw [if_pos he, if_pos he, mul_left_comm, ← Complex.ofReal_mul]
      rw [show (u (.inr (e, b))) * (stabilizerAxisExpectation (p e.castSucc) (some b.1) *
        stabilizerAxisExpectation (p e.succ) (some b.2)) = _ from alignedBondProbe_value u r a b e he]
      by_cases hb : b = a <;> simp [hb]
    · simp [he]
  have hpair (e : Fin (n + 1)) :
      (∑ b : Fin 3 × Fin 3, (u (.inr (e, b)) : ℂ) *
        L (finitePauliMatrix (couplingWord e b))) =
      4 * ((if (e.val + r.val) % 2 = 0 then |u (.inr (e, a))| else 0 : ℝ) : ℂ) := by
    simp_rw [hsingle]
    by_cases he : (e.val + r.val) % 2 = 0
    · simp [he]
    · simp [he]
  have hL : L (pathHamiltonian u) = (4 * S : ℝ) := by
    simp only [pathHamiltonian, onsitePart, edgePart, map_add, map_sum, map_smul, smul_eq_mul,
      show ∀ s b, L (finitePauliMatrix (onsiteWord s b)) = 0 from alternatingProbe_onsite p r,
      mul_zero, Finset.sum_const_zero, zero_add, hpair, S, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum]
  have h := norm_alternatingProbe_le p r (pathHamiltonian u)
  change ‖L (pathHamiltonian u)‖ ≤ _ at h
  rw [hL, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by norm_num) hS)] at h
  change S ≤ _
  linarith only [h]

/-- Alternating bond magnitudes of a coefficient difference give the same
lower bound for the distance of two path Hamiltonians. -/
theorem alternating_bond_abs_sum_le_pathHamiltonian_dist (u v : PathShell n)
    (r : Fin 2) (a : Fin 3 × Fin 3) :
    (∑ e : Fin (n + 1), if (e.val + r.val) % 2 = 0 then |u (.inr (e, a)) - v (.inr (e, a))| else 0) ≤
      ‖pathHamiltonian u - pathHamiltonian v‖ := by
  have h := alternating_bond_abs_sum_le_pathHamiltonian_norm (u - v) r a
  have he : pathHamiltonian (u - v) = pathHamiltonian u - pathHamiltonian v :=
    (pathHamiltonianLM n).map_sub u v
  rw [he] at h
  exact h

#print axioms alternating_bond_abs_sum_le_pathHamiltonian_norm
#print axioms alternating_bond_abs_sum_le_pathHamiltonian_dist

end

end GaloisForLFunctions.HTGeometry
