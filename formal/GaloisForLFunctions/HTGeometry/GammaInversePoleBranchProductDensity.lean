import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchCofinalDensity
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Independent Gamma pole tails detect mixed polynomial observables

One cofinally Zariski-dense pole tail detects every nonzero polynomial in one coefficient block.
Actual inverse words choose their pole labels independently.  This file proves the algebraic
product step: two independently chosen dense families detect every mixed polynomial in the sum of
their coordinate blocks.

Applied to normalized inverse-Gamma branches, arbitrary lower bounds may be imposed on both pole
labels.  Every nonzero mixed observable in two finite jet frames still survives.  The generic sum
theorem is the induction step for every finite inverse-word depth.
-/

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- A parameterized family detects every nonzero polynomial observable. -/
def ZariskiDetectingFamily {ι α : Type*} (x : ι → α → ℂ) : Prop :=
  ∀ P : MvPolynomial ι ℂ, P ≠ 0 →
    ∃ a : α, MvPolynomial.eval (fun i => x i a) P ≠ 0

/-- Every prescribed tail of a cofinally Zariski-dense sequence is a detecting family. -/
theorem CofinallyZariskiDense.zariskiDetectingFamily_tail
    {ι : Type*} {x : ι → ℕ → ℂ} (hx : CofinallyZariskiDense x) (N : ℕ) :
    ZariskiDetectingFamily
      (fun i (n : {n : ℕ // N ≤ n}) => x i n) := by
  intro P hP
  obtain ⟨n, hn, hdetect⟩ := hx P hP N
  exact ⟨⟨n, hn⟩, hdetect⟩

/-- The Cartesian product of two polynomial-detecting families detects every nonzero mixed
polynomial in the sum of their variable blocks. -/
theorem ZariskiDetectingFamily.sum
    {ι κ α β : Type*} {x : ι → α → ℂ} {y : κ → β → ℂ}
    (hx : ZariskiDetectingFamily x) (hy : ZariskiDetectingFamily y) :
    ZariskiDetectingFamily
      (fun q (ab : α × β) => Sum.elim (fun i => x i ab.1) (fun k => y k ab.2) q) := by
  intro P hP
  let Q : MvPolynomial ι (MvPolynomial κ ℂ) :=
    MvPolynomial.sumAlgEquiv ℂ ι κ P
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hP
    apply (MvPolynomial.sumAlgEquiv ℂ ι κ).injective
    simpa [Q] using hzero
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hcoeff : MvPolynomial.coeff e Q ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using he
  obtain ⟨b, hb⟩ := hy (MvPolynomial.coeff e Q) hcoeff
  let Qb : MvPolynomial ι ℂ :=
    MvPolynomial.map (MvPolynomial.eval (fun k => y k b)) Q
  have hQb : Qb ≠ 0 := by
    intro hzero
    have hcoeffzero := congrArg (MvPolynomial.coeff e) hzero
    rw [MvPolynomial.coeff_zero, Qb, MvPolynomial.coeff_map] at hcoeffzero
    exact hb hcoeffzero
  obtain ⟨a, ha⟩ := hx Qb hQb
  refine ⟨(a, b), ?_⟩
  let lhs : MvPolynomial (ι ⊕ κ) ℂ →+* ℂ :=
    MvPolynomial.eval (Sum.elim (fun i => x i a) (fun k => y k b))
  let rhs : MvPolynomial (ι ⊕ κ) ℂ →+* ℂ :=
    (MvPolynomial.eval (fun i => x i a)).comp
      ((MvPolynomial.map (MvPolynomial.eval (fun k => y k b))).comp
        (MvPolynomial.sumAlgEquiv ℂ ι κ).toRingHom)
  have heval : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs]
    · intro q
      cases q with
      | inl i => simp [lhs, rhs]
      | inr k => simp [lhs, rhs]
  change lhs P ≠ 0
  rw [heval]
  exact ha

/-- **Two-block cofinal Gamma horizon.**  Beyond arbitrary independent lower bounds on two pole
labels, every nonzero mixed polynomial observable in two normalized finite inverse-branch jet
frames is detected. -/
theorem gammaInversePoleBranchCoefficient_fin_twoBlock_detects
    (m : ℕ) (b : ℕ → ℕ → ℂ)
    (hb : ∀ j, (b j : NatGerm) = gammaInversePoleBranchCoefficientGerm j)
    (N₁ N₂ : ℕ) (P : MvPolynomial (Fin m ⊕ Fin m) ℂ) (hP : P ≠ 0) :
    ∃ n₁ n₂ : ℕ, N₁ ≤ n₁ ∧ N₂ ≤ n₂ ∧
      MvPolynomial.eval
        (Sum.elim (fun j : Fin m => b (j : ℕ) n₁)
          (fun j : Fin m => b (j : ℕ) n₂)) P ≠ 0 := by
  have hcofinal :=
    gammaInversePoleBranchCoefficient_fin_cofinallyZariskiDense m b hb
  have hleft := hcofinal.zariskiDetectingFamily_tail N₁
  have hright := hcofinal.zariskiDetectingFamily_tail N₂
  obtain ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩, hdetect⟩ := hleft.sum hright P hP
  exact ⟨n₁, n₂, hn₁, hn₂, hdetect⟩

end

end GaloisForLFunctions
