import GaloisForLFunctions.HTGeometry.TwoLocalPauliLieGeneration
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected-graph local controllability

One-site Pauli generators together with two-site generators on the edges of a connected graph
generate the full traceless Lie algebra.  Two adjacent edges produce the two-site generators of the
far pair, so connectivity propagates every pair along a walk.
-/

open Finset Matrix QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

attribute [local instance 100] LieRing.ofAssociativeRing

section Strings

variable {n : ℕ}

/-- The Pauli string with one prescribed letter. -/
def siteString (i : Fin n) (p : Fin 4) : Fin n → Fin 4 :=
  fun m => if m = i then p else 0

/-- The Pauli string with two prescribed letters. -/
def pairString (i k : Fin n) (p d : Fin 4) : Fin n → Fin 4 :=
  fun m => if m = i then p else if m = k then d else 0

/-- The Pauli string with three prescribed letters. -/
def tripleString (i j k : Fin n) (p q d : Fin 4) : Fin n → Fin 4 :=
  fun m => if m = i then p else if m = j then q else if m = k then d else 0

theorem pauliSupport4_siteString {i : Fin n} {p : Fin 4} (hp : p ≠ 0) :
    pauliSupport4 (siteString i p) = {i} := by
  classical
  ext m
  rw [mem_pauliSupport4, Finset.mem_singleton, siteString]
  by_cases h : m = i <;> simp [h, hp]

theorem pauliSupport4_pairString {i k : Fin n} (hik : i ≠ k) {p d : Fin 4} (hp : p ≠ 0)
    (hd : d ≠ 0) : pauliSupport4 (pairString i k p d) = {i, k} := by
  classical
  ext m
  rw [mem_pauliSupport4, Finset.mem_insert, Finset.mem_singleton, pairString]
  by_cases h : m = i
  · simp [h, hp]
  · by_cases h' : m = k <;> simp [h, h', hd, Ne.symm hik]

theorem siteString_ne_zero {i : Fin n} {p : Fin 4} (hp : p ≠ 0) : siteString i p ≠ 0 := by
  intro hc
  have := congrFun hc i
  rw [siteString, if_pos rfl] at this
  exact hp this

theorem pairString_ne_zero {i k : Fin n} {p d : Fin 4} (hp : p ≠ 0) :
    pairString i k p d ≠ 0 := by
  intro hc
  have := congrFun hc i
  rw [pairString, if_pos rfl] at this
  exact hp this

end Strings

section Omega

/-- Distinct nonzero single-qubit letters anticommute. -/
theorem omega4_eq_one_of_ne {a b : Fin 4} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    omega4 a b = 1 := by
  revert ha hb hab
  fin_cases a <;> fin_cases b <;> decide

theorem xor4_ne_zero_of_ne {a b : Fin 4} (hab : a ≠ b) : xor4 a b ≠ 0 := by
  revert hab
  fin_cases a <;> fin_cases b <;> decide

theorem exists_ne_zero_ne_ne (p : Fin 4) (hp : p ≠ 0) : ∃ a : Fin 4, a ≠ 0 ∧ a ≠ p := by
  fin_cases p
  · exact absurd rfl hp
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩

variable {n : ℕ}

theorem pauliOmega_eq_sum_of_support (s t : Fin n → Fin 4) (S : Finset (Fin n))
    (h : ∀ k, k ∉ S → omega4 (s k) (t k) = 0) :
    pauliOmega s t = ∑ k ∈ S, omega4 (s k) (t k) := by
  classical
  rw [pauliOmega]
  exact (Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => h k hk)).symm

end Omega

section Generation

variable {n : ℕ}

theorem pauliMat_xor_mem_of_anticomm
    {L : LieSubalgebra ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)}
    {u v : Fin n → Fin 4} (hu : pauliMat u ∈ L) (hv : pauliMat v ∈ L)
    (homega : pauliOmega u v = 1) : pauliMat (pauliXor u v) ∈ L := by
  have hbr : ⁅pauliMat u, pauliMat v⁆ ∈ L := L.lie_mem hu hv
  rw [pauliMat_bracket_closed] at hbr
  have hc : pauliPhase u v - pauliPhase v u ≠ 0 := pauliPhase_sub_ne_zero homega
  have hscaled := L.smul_mem (pauliPhase u v - pauliPhase v u)⁻¹ hbr
  simpa [hc] using hscaled

/-- Hermitian Pauli generators supported on a single site or on one graph edge. -/
def graphTwoLocalPauliMatrices (n : ℕ) (G : SimpleGraph (Fin n)) :
    Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4, s ≠ 0 ∧ pauliWeight4 s ≤ 2 ∧
    (∀ i ∈ pauliSupport4 s, ∀ j ∈ pauliSupport4 s, i ≠ j → G.Adj i j) ∧ A = pauliMat s}

variable (G : SimpleGraph (Fin n))

theorem siteString_mem_generators {i : Fin n} {p : Fin 4} (hp : p ≠ 0) :
    pauliMat (siteString i p) ∈ graphTwoLocalPauliMatrices n G := by
  classical
  refine ⟨siteString i p, siteString_ne_zero hp, ?_, ?_, rfl⟩
  · rw [pauliWeight4, pauliSupport4_siteString hp, Finset.card_singleton]
    omega
  · intro a ha b hb hab
    rw [pauliSupport4_siteString hp, Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab

theorem pairString_mem_generators {i k : Fin n} (hadj : G.Adj i k) {p d : Fin 4}
    (hp : p ≠ 0) (hd : d ≠ 0) :
    pauliMat (pairString i k p d) ∈ graphTwoLocalPauliMatrices n G := by
  classical
  have hik : i ≠ k := hadj.ne
  refine ⟨pairString i k p d, pairString_ne_zero hp, ?_, ?_, rfl⟩
  · rw [pauliWeight4, pauliSupport4_pairString hik hp hd]
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  · intro a ha b hb hab
    rw [pauliSupport4_pairString hik hp hd, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hadj
    · exact hadj.symm
    · exact absurd rfl hab


theorem xor4_xor_cancel (a b : Fin 4) : xor4 a (xor4 a b) = b := by
  revert b
  fin_cases a <;> decide

theorem xor4_zero_right' (a : Fin 4) : xor4 a 0 = a := by
  fin_cases a <;> decide

theorem xor4_self (a : Fin 4) : xor4 a a = 0 := by
  fin_cases a <;> decide

theorem omega4_zero_right' (a : Fin 4) : omega4 a 0 = 0 := by
  fin_cases a <;> decide

theorem omega4_zero_left' (a : Fin 4) : omega4 0 a = 0 := by
  fin_cases a <;> decide

theorem omega4_self' (a : Fin 4) : omega4 a a = 0 := by
  fin_cases a <;> decide

theorem xor4_zero_left' (a : Fin 4) : xor4 0 a = a := by
  fin_cases a <;> decide

theorem pauliXor_pairString_pairString {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a m m' d : Fin 4) :
    pauliXor (pairString i j a m) (pairString j k m' d) = tripleString i j k a (xor4 m m') d := by
  classical
  funext t
  simp only [pauliXor, pairString, tripleString]
  by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htk : t = k <;>
    simp [hti, htj, htk, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk,
      xor4_zero_right', xor4_zero_left', xor4_self]

theorem pauliXor_tripleString_pairString {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a a' q d : Fin 4) :
    pauliXor (tripleString i j k a q d) (pairString i j a' q) =
      pairString i k (xor4 a a') d := by
  classical
  funext t
  simp only [pauliXor, tripleString, pairString]
  by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htk : t = k <;>
    simp [hti, htj, htk, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk,
      xor4_zero_right', xor4_zero_left', xor4_self]

theorem pauliOmega_pairString_pairString {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a m m' d : Fin 4) :
    pauliOmega (pairString i j a m) (pairString j k m' d) = omega4 m m' := by
  classical
  rw [pauliOmega, Finset.sum_eq_single j]
  · simp [pairString, Ne.symm hij, hjk]
  · intro t _ htj
    simp only [pairString]
    by_cases hti : t = i <;> by_cases htk : t = k <;>
      simp [hti, htj, htk, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk,
        omega4_zero_right', omega4_zero_left']
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

theorem pauliOmega_tripleString_pairString {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a a' q d : Fin 4) :
    pauliOmega (tripleString i j k a q d) (pairString i j a' q) = omega4 a a' := by
  classical
  rw [pauliOmega, Finset.sum_eq_single i]
  · simp [tripleString, pairString, hij, hik]
  · intro t _ hti
    simp only [tripleString, pairString]
    by_cases htj : t = j <;> by_cases htk : t = k <;>
      simp [hti, htj, htk, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk,
        omega4_zero_right', omega4_zero_left', omega4_self']
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon


/-- **Two adjacent edges produce the two-site generators of the far pair.** -/
theorem pairString_mem_of_adj_of_mem {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hadj : G.Adj i j)
    (hmem : ∀ q e : Fin 4, q ≠ 0 → e ≠ 0 →
      pauliMat (pairString j k q e) ∈ dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G))
    (p d : Fin 4) (hp : p ≠ 0) (hd : d ≠ 0) :
    pauliMat (pairString i k p d) ∈ dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) := by
  classical
  obtain ⟨a, ha0, hap⟩ := exists_ne_zero_ne_ne p hp
  have ha'0 : xor4 a p ≠ 0 := xor4_ne_zero_of_ne hap
  have haa' : a ≠ xor4 a p := by
    intro hc
    have hcc : xor4 a a = xor4 a (xor4 a p) := by rw [← hc]
    rw [xor4_self, xor4_xor_cancel] at hcc
    exact hp hcc.symm
  have hxaa' : xor4 a (xor4 a p) = p := xor4_xor_cancel a p
  have hm : (1 : Fin 4) ≠ 0 := by decide
  have hm' : (2 : Fin 4) ≠ 0 := by decide
  have hmm' : (1 : Fin 4) ≠ 2 := by decide
  have hq0 : xor4 (1 : Fin 4) 2 ≠ 0 := xor4_ne_zero_of_ne hmm'
  have hs1 : pauliMat (pairString i j a 1) ∈
      dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) :=
    LieSubalgebra.subset_lieSpan (pairString_mem_generators G hadj ha0 hm)
  have hs2 : pauliMat (pairString j k 2 d) ∈
      dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) := hmem 2 d hm' hd
  have homega1 : pauliOmega (pairString i j a 1) (pairString j k 2 d) = 1 := by
    rw [pauliOmega_pairString_pairString hij hik hjk]
    exact omega4_eq_one_of_ne hm hm' hmm'
  have hu : pauliMat (tripleString i j k a (xor4 (1 : Fin 4) 2) d) ∈
      dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) := by
    have hxor := pauliMat_xor_mem_of_anticomm hs1 hs2 homega1
    rwa [pauliXor_pairString_pairString hij hik hjk] at hxor
  have hs3 : pauliMat (pairString i j (xor4 a p) (xor4 (1 : Fin 4) 2)) ∈
      dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) :=
    LieSubalgebra.subset_lieSpan (pairString_mem_generators G hadj ha'0 hq0)
  have homega2 : pauliOmega (tripleString i j k a (xor4 (1 : Fin 4) 2) d)
      (pairString i j (xor4 a p) (xor4 (1 : Fin 4) 2)) = 1 := by
    rw [pauliOmega_tripleString_pairString hij hik hjk]
    exact omega4_eq_one_of_ne ha0 ha'0 haa'
  have hfinal := pauliMat_xor_mem_of_anticomm hu hs3 homega2
  rwa [pauliXor_tripleString_pairString hij hik hjk, hxaa'] at hfinal

/-- Connectivity propagates the two-site generators along a walk. -/
theorem pairString_mem_of_walk : ∀ {i k : Fin n} (_ : G.Walk i k), i ≠ k →
    ∀ p d : Fin 4, p ≠ 0 → d ≠ 0 →
      pauliMat (pairString i k p d) ∈ dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) := by
  intro i k w
  induction w with
  | nil => intro hik; exact absurd rfl hik
  | @cons u v t hadj w ih =>
      intro hut p d hp hd
      by_cases hvt : v = t
      · subst hvt
        exact LieSubalgebra.subset_lieSpan (pairString_mem_generators G hadj hp hd)
      · exact pairString_mem_of_adj_of_mem G hadj.ne hut hvt hadj
          (fun q e hq he => ih hvt q e hq he) p d hp hd


theorem eq_siteString_of_support_eq_singleton {s : Fin n → Fin 4} {i : Fin n}
    (h : pauliSupport4 s = {i}) : s = siteString i (s i) := by
  classical
  funext t
  rw [siteString]
  by_cases hti : t = i
  · rw [if_pos hti, hti]
  · rw [if_neg hti]
    by_contra hc
    have : t ∈ pauliSupport4 s := mem_pauliSupport4 s t |>.mpr hc
    rw [h, Finset.mem_singleton] at this
    exact hti this

theorem eq_pairString_of_support_eq_pair {s : Fin n → Fin 4} {i k : Fin n}
    (h : pauliSupport4 s = {i, k}) : s = pairString i k (s i) (s k) := by
  classical
  funext t
  rw [pairString]
  by_cases hti : t = i
  · rw [if_pos hti, hti]
  · rw [if_neg hti]
    by_cases htk : t = k
    · rw [if_pos htk, htk]
    · rw [if_neg htk]
      by_contra hc
      have hmem : t ∈ pauliSupport4 s := mem_pauliSupport4 s t |>.mpr hc
      rw [h, Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem.elim hti htk

theorem twoLocal_subset_graphLie (hconn : G.Connected) :
    twoLocalPauliMatrices n ⊆ dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) := by
  classical
  rintro _ ⟨s, hs, hweight, rfl⟩
  have hne : (pauliSupport4 s).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    refine hs (funext fun t => ?_)
    by_contra hst
    have : t ∈ pauliSupport4 s := mem_pauliSupport4 s t |>.mpr hst
    rw [hc] at this
    exact absurd this (Finset.notMem_empty t)
  have hcard : (pauliSupport4 s).card = 1 ∨ (pauliSupport4 s).card = 2 := by
    have h1 : 1 ≤ (pauliSupport4 s).card := Finset.card_pos.mpr hne
    have h2 : (pauliSupport4 s).card ≤ 2 := hweight
    omega
  rcases hcard with hone | htwo
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    have hsi : s i ≠ 0 := by
      have : i ∈ pauliSupport4 s := by rw [hi]; exact Finset.mem_singleton_self i
      exact (mem_pauliSupport4 s i).mp this
    rw [eq_siteString_of_support_eq_singleton hi]
    exact LieSubalgebra.subset_lieSpan (siteString_mem_generators G hsi)
  · obtain ⟨i, k, hik, hpair⟩ := Finset.card_eq_two.mp htwo
    have hsi : s i ≠ 0 := by
      have : i ∈ pauliSupport4 s := by rw [hpair]; exact Finset.mem_insert_self i {k}
      exact (mem_pauliSupport4 s i).mp this
    have hsk : s k ≠ 0 := by
      have : k ∈ pauliSupport4 s := by
        rw [hpair]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
      exact (mem_pauliSupport4 s k).mp this
    rw [eq_pairString_of_support_eq_pair hpair]
    obtain ⟨w⟩ := hconn.preconnected i k
    exact pairString_mem_of_walk G w hik (s i) (s k) hsi hsk

/-- **Connected-graph local controllability.**

One-site Pauli generators together with the two-site generators on the edges of a connected graph
generate the full traceless Lie algebra. -/
theorem dynamicalLieAlgebra_graphTwoLocalPauliMatrices_eq_tracelessLie (hconn : G.Connected) :
    dynamicalLieAlgebra (graphTwoLocalPauliMatrices n G) = tracelessLie (2 ^ n) := by
  classical
  refine le_antisymm ?_ ?_
  · refine dynamicalLieAlgebra_minimal _ ?_
    rintro _ ⟨s, hs, _, _, rfl⟩
    change pauliMat s ∈ LinearMap.ker (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ)
    rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply, pauliMat_trace_eq_zero hs]
  · rw [← dynamicalLieAlgebra_twoLocalPauliMatrices_eq_tracelessLie n]
    exact dynamicalLieAlgebra_minimal _ (twoLocal_subset_graphLie G hconn)

end Generation

end GaloisForLFunctions.HTGeometry
