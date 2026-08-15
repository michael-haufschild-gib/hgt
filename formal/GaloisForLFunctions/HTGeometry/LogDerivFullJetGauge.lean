import GaloisForLFunctions.HTGeometry.FullExponentialJetGauge
import GaloisForLFunctions.HTGeometry.LogDerivFamilyRealization

/-!
# The full jet gauge of a logarithmic-derivative equation

For a family solving `E' = f^{(r)} E` every jet of `E` is `E` times a universal polynomial in the
jets of `f`, so the jet ring substitutes into a polynomial ring with one extra variable per member.
The substitution is injective as soon as prescribed jets with nonzero value can be realized, which
is the analytic input supplied separately for each `r`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The blockwise numerator in the full jet ring. -/
def fullLogJetNum (r m : ℕ) (i : Fin m) (k : ℕ) : MvPolynomial (FullJetIndex m) ℂ :=
  MvPolynomial.rename (fun j => Sum.inr (i, j)) (logJetNum r k)

theorem eval_fullLogJetNum {r m : ℕ} (base : Fin m → ℂ → ℂ) (z : ℂ) (i : Fin m) (k : ℕ) :
    MvPolynomial.eval (fullJetVec base z) (fullLogJetNum r m i k)
      = MvPolynomial.eval (jetVec (base i) z) (logJetNum r k) := by
  rw [fullLogJetNum, MvPolynomial.eval_rename]
  rfl

/-- **The jets of a logarithmic-derivative family.** -/
theorem fullJetVec_logDeriv_apply {r m : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {base sol : Fin m → ℂ → ℂ}
    (hb : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (base i) w)
    (hs : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sol i) w)
    (hrel : ∀ i, ∀ w ∈ U, deriv (sol i) w = iteratedDeriv r (base i) w * sol i w)
    {z : ℂ} (hz : z ∈ U) (i : Fin m) (k : ℕ) :
    fullJetVec sol z (Sum.inr (i, k))
      = sol i z * MvPolynomial.eval (fullJetVec base z) (fullLogJetNum r m i k) := by
  rw [fullJetVec_inr, eval_fullLogJetNum,
    iteratedDeriv_eq_logJetNum_mul hU (hb i) (hs i) r (hrel i) k z hz]

/-- The jet ring of the bases with one solution variable per member. -/
abbrev FullLogRing (m : ℕ) := MvPolynomial (Fin m) (MvPolynomial (FullJetIndex m) ℂ)

/-- The logarithmic-derivative substitution on full jet coordinates. -/
def fullLogSubst (r m : ℕ) : FullJetIndex m → FullLogRing m :=
  Sum.elim (fun _ => MvPolynomial.C (MvPolynomial.X (Sum.inl ())))
    (fun p => MvPolynomial.X p.1 * MvPolynomial.C (fullLogJetNum r m p.1 p.2))

/-- The substitution as a ring homomorphism. -/
def fullLogSubstHom (r m : ℕ) : MvPolynomial (FullJetIndex m) ℂ →+* FullLogRing m :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) (fullLogSubst r m)

@[simp] theorem fullLogSubstHom_X {r m : ℕ} (v : FullJetIndex m) :
    fullLogSubstHom r m (MvPolynomial.X v) = fullLogSubst r m v := by
  rw [fullLogSubstHom, MvPolynomial.eval₂Hom_X']

@[simp] theorem fullLogSubstHom_C {r m : ℕ} (c : ℂ) :
    fullLogSubstHom r m (MvPolynomial.C c) = MvPolynomial.C (MvPolynomial.C c) := by
  rw [fullLogSubstHom, MvPolynomial.eval₂Hom_C]
  rfl

/-- The jet point of a logarithmic-derivative family. -/
def logFullJetPoint (r : ℕ) {m : ℕ} (x : FullJetIndex m → ℂ) (u : Fin m → ℂ) :
    FullJetIndex m → ℂ :=
  Sum.elim (fun _ => x (Sum.inl ()))
    (fun p => u p.1 * MvPolynomial.eval x (fullLogJetNum r m p.1 p.2))

theorem eval₂_fullLogSubstHom {r m : ℕ} (x : FullJetIndex m → ℂ) (u : Fin m → ℂ)
    (P : MvPolynomial (FullJetIndex m) ℂ) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) u (fullLogSubstHom r m P)
      = MvPolynomial.eval (logFullJetPoint r x u) P := by
  have hcomp : ((MvPolynomial.eval₂Hom (MvPolynomial.eval x) u : FullLogRing m →+* ℂ).comp
        (fullLogSubstHom r m))
      = (MvPolynomial.eval (logFullJetPoint r x u) : MvPolynomial (FullJetIndex m) ℂ →+* ℂ) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · rw [RingHom.comp_apply, fullLogSubstHom_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C,
        MvPolynomial.eval_C]
    · rw [RingHom.comp_apply, fullLogSubstHom_X, MvPolynomial.eval_X]
      rcases v with u' | ⟨i, k⟩
      · rw [fullLogSubst, Sum.elim_inl, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_X]
        rfl
      · rw [fullLogSubst, Sum.elim_inr, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
        rfl
  exact congrArg (fun f : MvPolynomial (FullJetIndex m) ℂ →+* ℂ => f P) hcomp

theorem fullLogSubstHom_injective (r m : ℕ)
    (hreal : ∀ (n : ℕ) (z₀ : ℂ) (y : Fin m → ℕ → ℂ), (∀ i, y i 0 ≠ 0) →
      ∃ (V : Set ℂ) (base sol : Fin m → ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧
        (∀ i, ∀ w ∈ V, ContDiffAt ℂ (⊤ : ℕ∞) (base i) w) ∧
        (∀ i, ∀ w ∈ V, ContDiffAt ℂ (⊤ : ℕ∞) (sol i) w) ∧
        (∀ i, ∀ w ∈ V, deriv (sol i) w = iteratedDeriv r (base i) w * sol i w) ∧
        (∀ i, ∀ k ≤ n, iteratedDeriv k (sol i) z₀ = y i k)) :
    Function.Injective (fullLogSubstHom r m) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  refine mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates
    (Finset.image (fun i : Fin m => (Sum.inr (i, 0) : FullJetIndex m)) Finset.univ) P ?_
  intro y hy
  have hy0 : ∀ i : Fin m, y (Sum.inr (i, 0)) ≠ 0 := fun i =>
    hy _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  set n : ℕ := fullJetOrder P with hn
  set z₀ : ℂ := y (Sum.inl ()) with hz₀
  set c : Fin m → ℕ → ℂ := fun i k => if k ≤ n then y (Sum.inr (i, k)) else 1 with hc
  have hcne : ∀ i, c i 0 ≠ 0 := by
    intro i
    rw [hc]
    simp only [Nat.zero_le, if_pos]
    exact hy0 i
  obtain ⟨V, base, sol, hVopen, hz₀V, hbase, hsol, hrelV, hjets⟩ :=
    hreal n z₀ c hcne
  set x : FullJetIndex m → ℂ := fullJetVec base z₀ with hx
  set u : Fin m → ℂ := fun i => sol i z₀ with hu
  have hpoint : ∀ v ∈ P.vars, logFullJetPoint r x u v = y v := by
    intro v hv
    rcases v with u' | ⟨i, k⟩
    · rw [logFullJetPoint, Sum.elim_inl, hx, fullJetVec_inl]
    · have hk : k ≤ n := le_fullJetOrder hv
      have hexp : logFullJetPoint r x u (Sum.inr (i, k))
          = fullJetVec sol z₀ (Sum.inr (i, k)) := by
        rw [fullJetVec_logDeriv_apply hVopen hbase hsol hrelV hz₀V i k, logFullJetPoint,
          Sum.elim_inr]
      rw [hexp]
      have hval : fullJetVec sol z₀ (Sum.inr (i, k)) = iteratedDeriv k (sol i) z₀ := rfl
      rw [hval, hjets i k hk, hc]
      simp only [hk, if_pos]
  have hcongr : MvPolynomial.eval (logFullJetPoint r x u) P = MvPolynomial.eval y P := by
    refine MvPolynomial.eval₂_congr _ _ _ ?_
    intro v d hvd hcoeff
    exact hpoint v ((MvPolynomial.mem_vars_iff_mem_support v).mpr
      ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, hvd⟩)
  rw [← hcongr, ← eval₂_fullLogSubstHom x u P, hP]
  exact MvPolynomial.eval₂_zero _ _


/-- **The carrier substitution on full jets is injective.** -/
theorem fullLogSubstHom_injective_zero (m : ℕ) : Function.Injective (fullLogSubstHom 0 m) := by
  refine fullLogSubstHom_injective 0 m ?_
  intro n z₀ y hy
  obtain ⟨V, H, E, hVo, hz, hH, hE, _hEne, hrel, hjet⟩ :=
    exists_logDerivFamily_realizing_jets n z₀ y hy
  exact ⟨V, H, E, hVo, hz, hH, hE, hrel, hjet⟩

end

end GaloisForLFunctions.HTGeometry
