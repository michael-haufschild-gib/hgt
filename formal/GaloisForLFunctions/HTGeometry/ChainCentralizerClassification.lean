import GaloisForLFunctions.HTGeometry.ChainTwoSiteRelation
import GaloisForLFunctions.HTGeometry.EdgeCouplingSynchronization

/-!
# The centralizer of an open-chain two-local operator

An open-chain two-local operator with invertible edge couplings, one of them field rigid, commutes
inside the two-local shell only with its own real multiples up to a scalar: the coupling matrices
of any commuting shell operator are a common multiple of the original ones, and its one-site fields
are the same multiple of the original one-site fields.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {m : ℕ}

theorem chainSiteOp_add (h g : Fin (m + 1) → Fin 3 → ℝ) :
    chainSiteOp (fun s a => h s a + g s a) = chainSiteOp h + chainSiteOp g := by
  rw [chainSiteOp, chainSiteOp, chainSiteOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem chainSiteOp_smul (c : ℝ) (h : Fin (m + 1) → Fin 3 → ℝ) :
    chainSiteOp (fun s a => c * h s a) = (c : ℂ) • chainSiteOp h := by
  rw [chainSiteOp, chainSiteOp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem chainEdgeOp_smul (c : ℝ) (J : Fin m → Fin 3 → Fin 3 → ℝ) :
    chainEdgeOp (fun v a b => c * J v a b) = (c : ℂ) • chainEdgeOp J := by
  rw [chainEdgeOp, chainEdgeOp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem det_ne_zero_of_isUnit {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsUnit A.det) : A ≠ 0 := by
  intro hc
  rw [hc, Matrix.det_zero] at hA
  exact absurd hA (by simp)

theorem mul_comm_of_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (A S : Matrix n n ℂ) (c : ℂ) (h : A * (S + c • A) = (S + c • A) * A) : A * S = S * A := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] at h
  exact add_right_cancel h

/-- **The centralizer of a chain shell operator inside the shell.**

If two open-chain two-local operators commute, the first has invertible edge couplings and at least
one field-rigid edge, then the second is a real multiple of the first, up to a multiple of the
identity (which is invisible in the coefficients). -/
theorem exists_scalar_of_commute_chain (hm : 2 ≤ m) (h1 h2 : Fin (m + 1) → Fin 3 → ℝ)
    (J K : Fin m → Fin 3 → Fin 3 → ℝ)
    (hJdet : ∀ v : Fin m, IsUnit (Matrix.det (J v)))
    (v0 : Fin m) (hrigid : FieldRigid (J v0))
    (hcomm : (chainSiteOp h1 + chainEdgeOp J) * (chainSiteOp h2 + chainEdgeOp K) =
      (chainSiteOp h2 + chainEdgeOp K) * (chainSiteOp h1 + chainEdgeOp J)) :
    ∃ c : ℝ, (∀ v : Fin m, K v = c • J v) ∧ (∀ (s : Fin (m + 1)) (a : Fin 3),
      h2 s a = c * h1 s a) := by
  classical
  obtain ⟨Jn, hJn⟩ : ∃ Jn : ℕ → Matrix (Fin 3) (Fin 3) ℝ,
      ∀ (v : ℕ) (hv : v < m), Jn v = J ⟨v, hv⟩ :=
    ⟨fun v => if h : v < m then J ⟨v, h⟩ else 0, fun v hv => dif_pos hv⟩
  obtain ⟨Kn, hKn⟩ : ∃ Kn : ℕ → Matrix (Fin 3) (Fin 3) ℝ,
      ∀ (v : ℕ) (hv : v < m), Kn v = K ⟨v, hv⟩ :=
    ⟨fun v => if h : v < m then K ⟨v, h⟩ else 0, fun v hv => dif_pos hv⟩
  -- Step 1: the consecutive-edge three-body relations synchronize the couplings.
  have hstep : ∀ v : ℕ, ∃ l : ℝ,
      v + 1 < m → (Kn v = l • Jn v ∧ Kn (v + 1) = l • Jn (v + 1)) := by
    intro v
    by_cases hv : v + 1 < m
    · have hv0 : v < m := by omega
      have hrel : ∀ a e : Fin 3,
          crossProduct (fun b => J ⟨v, hv0⟩ a b) (fun d => K ⟨v + 1, hv⟩ d e) =
            crossProduct (fun b => K ⟨v, hv0⟩ a b) (fun d => J ⟨v + 1, hv⟩ d e) := by
        intro a e
        funext f
        exact crossProduct_chain_eq h1 h2 J K hcomm (p := ⟨v, hv0⟩) (q := ⟨v + 1, hv⟩) rfl a e f
      obtain ⟨l, hl1, hl2⟩ := exists_scalar_of_row_col_cross (J ⟨v, hv0⟩) (J ⟨v + 1, hv⟩)
        (K ⟨v, hv0⟩) (K ⟨v + 1, hv⟩) (hJdet _) (hJdet _) hrel
      refine ⟨l, fun _ => ⟨?_, ?_⟩⟩
      · rw [hKn v hv0, hJn v hv0, hl1]
      · rw [hKn (v + 1) hv, hJn (v + 1) hv, hl2]
    · exact ⟨0, fun hc => absurd hc hv⟩
  choose lam hlam using hstep
  have hJne : ∀ v : ℕ, v < m → Jn v ≠ 0 := by
    intro v hv
    rw [hJn v hv]
    exact det_ne_zero_of_isUnit (hJdet _)
  obtain ⟨c, hc⟩ := exists_common_scalar_of_chain m hm Jn Kn lam hJne
    (fun v hv => (hlam v hv).1) (fun v hv => (hlam v hv).2)
  have hKeq : ∀ v : Fin m, K v = c • J v := by
    intro v
    have hv := hc v.val v.isLt
    rw [hKn v.val v.isLt, hJn v.val v.isLt] at hv
    exact hv
  refine ⟨c, hKeq, ?_⟩
  -- Step 2: subtracting the synchronized part leaves a purely one-site operator.
  obtain ⟨r, hr⟩ : ∃ r : ℕ → (Fin 3 → ℝ),
      ∀ (v : ℕ) (hv : v < m + 1), r v = fun a => h2 ⟨v, hv⟩ a - c * h1 ⟨v, hv⟩ a :=
    ⟨fun v => if h : v < m + 1 then (fun a => h2 ⟨v, h⟩ a - c * h1 ⟨v, h⟩ a) else 0,
      fun v hv => dif_pos hv⟩
  have hsplit : chainSiteOp h2 + chainEdgeOp K =
      chainSiteOp (fun s a => h2 s a - c * h1 s a) +
        (c : ℂ) • (chainSiteOp h1 + chainEdgeOp J) := by
    have hK : chainEdgeOp K = (c : ℂ) • chainEdgeOp J := by
      rw [← chainEdgeOp_smul c J]
      congr 1
      funext v a b
      simpa using congrFun (congrFun (hKeq v) a) b
    have hS : chainSiteOp h2 =
        chainSiteOp (fun s a => h2 s a - c * h1 s a) + (c : ℂ) • chainSiteOp h1 := by
      rw [← chainSiteOp_smul c h1, ← chainSiteOp_add]
      congr 1
      funext s a
      ring
    rw [hK, hS, smul_add]
    abel
  have hcomm' : (chainSiteOp h1 + chainEdgeOp J) *
      chainSiteOp (fun s a => h2 s a - c * h1 s a) =
      chainSiteOp (fun s a => h2 s a - c * h1 s a) * (chainSiteOp h1 + chainEdgeOp J) := by
    rw [hsplit] at hcomm
    exact mul_comm_of_add_smul _ _ _ hcomm
  have hzero : ∀ v : ℕ, v < m →
      fieldMap (Jn v) (r v) (r (v + 1)) = 0 := by
    intro v hv
    have hv1 : v < m + 1 := by omega
    have hv2 : v + 1 < m + 1 := by omega
    have hfm := fieldMap_eq_zero_of_commute h1 (fun s a => h2 s a - c * h1 s a) J hcomm' ⟨v, hv⟩
    have hcast : ((⟨v, hv⟩ : Fin m).castSucc : Fin (m + 1)) = ⟨v, hv1⟩ := Fin.ext (by simp)
    have hsucc : ((⟨v, hv⟩ : Fin m).succ : Fin (m + 1)) = ⟨v + 1, hv2⟩ := Fin.ext (by simp)
    rw [hcast, hsucc] at hfm
    rw [hJn v hv, hr v hv1, hr (v + 1) hv2]
    exact hfm
  obtain hall := all_field_zero_of_chain m Jn r
    (fun v hv => by rw [hJn v hv]; exact hJdet _) hzero v0.val v0.isLt
    (by rw [hJn v0.val v0.isLt]; simpa using hrigid)
  intro s a
  have hs := hall s.val (by omega)
  rw [hr s.val s.isLt] at hs
  have hval := congrFun hs a
  simp only [Fin.eta, Pi.zero_apply] at hval
  linarith [hval]

end GaloisForLFunctions.HTGeometry
