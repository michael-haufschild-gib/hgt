import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import GaloisForLFunctions.HTGeometry.ResultantDegreeBound

/-!
# Eliminating one variable from a multivariate system

Splitting off the first variable presents a polynomial in `m + 1` variables as a polynomial in that
variable with coefficients in the remaining `m`.  The resultant of two such presentations lies in
the ideal the two generate, so it vanishes on the projection of every common zero: one variable is
eliminated and the remaining ones are confined to a hypersurface.

This is the inductive step of elimination, and mathlib has nothing of the kind — only the resultant
itself and its Bézout identity.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [CommRing K] {m : ℕ}

/-- **Evaluating a polynomial in the split presentation**: the outer variable at `y`, the remaining
ones at `s`. -/
noncomputable def mvEvalHom (s : Fin m → K) (y : K) : (MvPolynomial (Fin m) K)[X] →+* K :=
  (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (MvPolynomial.eval s))

theorem mvEvalHom_C (s : Fin m → K) (y : K) (r : MvPolynomial (Fin m) K) :
    mvEvalHom s y (Polynomial.C r) = MvPolynomial.eval s r := by
  simp [mvEvalHom]

theorem mvEvalHom_finSuccEquiv (s : Fin m → K) (y : K) (f : MvPolynomial (Fin (m + 1)) K) :
    mvEvalHom s y (MvPolynomial.finSuccEquiv K m f)
      = MvPolynomial.eval (Fin.cons y s) f := by
  rw [mvEvalHom, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
    ← MvPolynomial.eval_eq_eval_mv_eval']

/-- **The eliminant of a two-member system vanishes on the projection of every common zero.** -/
theorem eval_resultant_eq_zero_of_mv_common_zero (f g : MvPolynomial (Fin (m + 1)) K) {a b : ℕ}
    (hf : (MvPolynomial.finSuccEquiv K m f).natDegree ≤ a)
    (hg : (MvPolynomial.finSuccEquiv K m g).natDegree ≤ b) (H : a ≠ 0 ∨ b ≠ 0)
    (s : Fin m → K) (y : K)
    (hfx : MvPolynomial.eval (Fin.cons y s) f = 0)
    (hgx : MvPolynomial.eval (Fin.cons y s) g = 0) :
    MvPolynomial.eval s (Polynomial.resultant (MvPolynomial.finSuccEquiv K m f)
      (MvPolynomial.finSuccEquiv K m g) a b) = 0 := by
  obtain ⟨p, q, -, -, he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (MvPolynomial.finSuccEquiv K m f) (MvPolynomial.finSuccEquiv K m g) hf hg H
  have hval := congrArg (mvEvalHom s y) he
  rw [mvEvalHom_C, map_add, map_mul, map_mul, mvEvalHom_finSuccEquiv, mvEvalHom_finSuccEquiv,
    hfx, hgx, zero_mul, zero_mul, add_zero] at hval
  exact hval.symm

/-- **A nontrivial eliminant confines the projections of the common zeros to a hypersurface.** -/
theorem exists_ne_zero_vanishing_on_projection (f g : MvPolynomial (Fin (m + 1)) K) {a b : ℕ}
    (hf : (MvPolynomial.finSuccEquiv K m f).natDegree ≤ a)
    (hg : (MvPolynomial.finSuccEquiv K m g).natDegree ≤ b) (H : a ≠ 0 ∨ b ≠ 0)
    (hres : Polynomial.resultant (MvPolynomial.finSuccEquiv K m f)
      (MvPolynomial.finSuccEquiv K m g) a b ≠ 0) :
    ∃ R : MvPolynomial (Fin m) K, R ≠ 0 ∧
      ∀ (s : Fin m → K) (y : K), MvPolynomial.eval (Fin.cons y s) f = 0 →
        MvPolynomial.eval (Fin.cons y s) g = 0 → MvPolynomial.eval s R = 0 :=
  ⟨_, hres, fun s y hfx hgx =>
    eval_resultant_eq_zero_of_mv_common_zero f g hf hg H s y hfx hgx⟩


/-! ## Degrees of a multivariate determinant -/

section Degree

variable {ι : Type*} {N : ℕ}

/-- **The weighted degree bound for a determinant of multivariate polynomials.**  Zero entries are
allowed explicitly, since a zero multivariate polynomial has total degree zero rather than `⊥`. -/
theorem totalDegree_det_add_le (M : Matrix (Fin N) (Fin N) (MvPolynomial ι K)) (c : Fin N → ℕ)
    (h : ∀ i j, M i j = 0 ∨ (M i j).totalDegree + (i : ℕ) ≤ c j) :
    M.det = 0 ∨ M.det.totalDegree + (∑ i : Fin N, (i : ℕ)) ≤ ∑ j, c j := by
  classical
  by_cases hall : ∀ σ : Equiv.Perm (Fin N), (∏ i, M (σ i) i) = 0
  · left
    rw [Matrix.det_apply']
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [hall σ, mul_zero]
  · right
    push Not at hall
    obtain ⟨σ₀, hσ₀⟩ := hall
    have hfac : ∀ i, M (σ₀ i) i ≠ 0 := fun i hi =>
      hσ₀ (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hperm : (∑ i : Fin N, (i : ℕ)) = ∑ i : Fin N, ((σ₀ i : ℕ)) :=
      (Equiv.sum_comp σ₀ (fun i : Fin N => (i : ℕ))).symm
    have hsum0 : (∑ i : Fin N, (i : ℕ)) ≤ ∑ j, c j := by
      rw [hperm]
      refine Finset.sum_le_sum fun i _ => ?_
      rcases h (σ₀ i) i with h0 | h1
      · exact absurd h0 (hfac i)
      · omega
    have hterm : ∀ σ : Equiv.Perm (Fin N),
        ((((Equiv.Perm.sign σ : ℤ) : MvPolynomial ι K)) * ∏ i, M (σ i) i).totalDegree
          + (∑ i : Fin N, (i : ℕ)) ≤ ∑ j, c j := by
      intro σ
      have hprod : (∏ i, M (σ i) i).totalDegree + (∑ i : Fin N, (i : ℕ)) ≤ ∑ j, c j := by
        by_cases hz : (∏ i, M (σ i) i) = 0
        · rw [hz, MvPolynomial.totalDegree_zero, zero_add]
          exact hsum0
        · have hfacσ : ∀ i, M (σ i) i ≠ 0 := fun i hi =>
            hz (Finset.prod_eq_zero (Finset.mem_univ i) hi)
          have hperm' : (∑ i : Fin N, (i : ℕ)) = ∑ i : Fin N, ((σ i : ℕ)) :=
            (Equiv.sum_comp σ (fun i : Fin N => (i : ℕ))).symm
          calc (∏ i, M (σ i) i).totalDegree + (∑ i : Fin N, (i : ℕ))
              ≤ (∑ i : Fin N, (M (σ i) i).totalDegree) + (∑ i : Fin N, ((σ i : ℕ))) := by
                rw [hperm']
                exact Nat.add_le_add_right (MvPolynomial.totalDegree_finsetProd _ _) _
            _ = ∑ i : Fin N, ((M (σ i) i).totalDegree + ((σ i : ℕ))) :=
                (Finset.sum_add_distrib).symm
            _ ≤ ∑ j, c j := by
                refine Finset.sum_le_sum fun i _ => ?_
                rcases h (σ i) i with h0 | h1
                · exact absurd h0 (hfacσ i)
                · exact h1
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
      · rw [hσ]
        simpa using hprod
      · rw [hσ]
        have hne : ((((-1 : ℤˣ) : ℤ) : MvPolynomial ι K)) * (∏ i, M (σ i) i)
            = -(∏ i, M (σ i) i) := by
          push_cast
          ring
        rw [hne, MvPolynomial.totalDegree_neg]
        exact hprod
    obtain ⟨σ₁, -, hσ₁⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Equiv.Perm (Fin N)))
      ⟨1, Finset.mem_univ 1⟩
      (fun σ => ((((Equiv.Perm.sign σ : ℤ) : MvPolynomial ι K)) * ∏ i, M (σ i) i).totalDegree)
    calc M.det.totalDegree + (∑ i : Fin N, (i : ℕ))
        ≤ (Finset.univ.sup fun σ : Equiv.Perm (Fin N) =>
              ((((Equiv.Perm.sign σ : ℤ) : MvPolynomial ι K)) * ∏ i, M (σ i) i).totalDegree)
            + (∑ i : Fin N, (i : ℕ)) := by
          refine Nat.add_le_add_right ?_ _
          rw [Matrix.det_apply']
          exact MvPolynomial.totalDegree_finsetSum _ _
      _ = ((((Equiv.Perm.sign σ₁ : ℤ) : MvPolynomial ι K)) * ∏ i, M (σ₁ i) i).totalDegree
            + (∑ i : Fin N, (i : ℕ)) := by rw [hσ₁]
      _ ≤ ∑ j, c j := hterm σ₁

end Degree


/-! ## The degree of the eliminant -/

section EliminantDegree

variable {a b : ℕ}

/-- **The entries of the Sylvester matrix of a split multivariate pair obey the weighted degree
bound.** -/
theorem totalDegree_sylvester_finSuccEquiv_add_le {f g : MvPolynomial (Fin (m + 1)) K}
    (hf : f.totalDegree ≤ a) (hg : g.totalDegree ≤ b) (p q : ℕ) (i j : Fin (p + q)) :
    Polynomial.sylvester (MvPolynomial.finSuccEquiv K m f) (MvPolynomial.finSuccEquiv K m g) p q
        i j = 0 ∨
      (Polynomial.sylvester (MvPolynomial.finSuccEquiv K m f)
        (MvPolynomial.finSuccEquiv K m g) p q i j).totalDegree + (i : ℕ)
        ≤ sylvesterWeight a b p q j := by
  classical
  refine Fin.addCases (fun j₁ => ?_) (fun j₁ => ?_) j
  · rw [sylvesterWeight_castAdd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    by_cases hmem : (i : ℕ) ∈ Set.Icc ((j₁ : ℕ)) ((j₁ : ℕ) + q)
    · by_cases hc0 : ((MvPolynomial.finSuccEquiv K m) g).coeff ((i : ℕ) - (j₁ : ℕ)) = 0
      · exact Or.inl (by rw [if_pos hmem, hc0])
      · refine Or.inr ?_
        rw [if_pos hmem]
        have hji : (j₁ : ℕ) ≤ (i : ℕ) := hmem.1
        have hcoeff := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le g
          ((i : ℕ) - (j₁ : ℕ)) hc0
        omega
    · exact Or.inl (by rw [if_neg hmem])
  · rw [sylvesterWeight_natAdd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    by_cases hmem : (i : ℕ) ∈ Set.Icc ((j₁ : ℕ)) ((j₁ : ℕ) + p)
    · by_cases hc0 : ((MvPolynomial.finSuccEquiv K m) f).coeff ((i : ℕ) - (j₁ : ℕ)) = 0
      · exact Or.inl (by rw [if_pos hmem, hc0])
      · refine Or.inr ?_
        rw [if_pos hmem]
        have hji : (j₁ : ℕ) ≤ (i : ℕ) := hmem.1
        have hcoeff := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f
          ((i : ℕ) - (j₁ : ℕ)) hc0
        omega
    · exact Or.inl (by rw [if_neg hmem])

/-- **The eliminant of a split multivariate pair has the classical degree.**  Either it vanishes
identically, or its total degree plus `p q` is at most `p b + q a`. -/
theorem totalDegree_resultant_finSuccEquiv_add_le {f g : MvPolynomial (Fin (m + 1)) K}
    (hf : f.totalDegree ≤ a) (hg : g.totalDegree ≤ b) (p q : ℕ) :
    Polynomial.resultant (MvPolynomial.finSuccEquiv K m f)
        (MvPolynomial.finSuccEquiv K m g) p q = 0 ∨
      (Polynomial.resultant (MvPolynomial.finSuccEquiv K m f)
        (MvPolynomial.finSuccEquiv K m g) p q).totalDegree + p * q ≤ p * b + q * a := by
  rcases totalDegree_det_add_le
      (Polynomial.sylvester (MvPolynomial.finSuccEquiv K m f)
        (MvPolynomial.finSuccEquiv K m g) p q)
      (sylvesterWeight a b p q)
      (totalDegree_sylvester_finSuccEquiv_add_le hf hg p q) with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have hsum := sum_sylvesterWeight_add a b p q
    have hdef : Polynomial.resultant (MvPolynomial.finSuccEquiv K m f)
        (MvPolynomial.finSuccEquiv K m g) p q
        = (Polynomial.sylvester (MvPolynomial.finSuccEquiv K m f)
            (MvPolynomial.finSuccEquiv K m g) p q).det := rfl
    rw [hdef]
    omega

end EliminantDegree


/-! ## One elimination step for a system -/

section System

theorem natDegree_finSuccEquiv_le_totalDegree (f : MvPolynomial (Fin (m + 1)) K) :
    (MvPolynomial.finSuccEquiv K m f).natDegree ≤ f.totalDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hdeg : (MvPolynomial.finSuccEquiv K m f).degree = MvPolynomial.degreeOf 0 f :=
      MvPolynomial.degree_finSuccEquiv hf
    have hnat : (MvPolynomial.finSuccEquiv K m f).natDegree = MvPolynomial.degreeOf 0 f :=
      Polynomial.natDegree_eq_of_degree_eq_some hdeg
    rw [hnat]
    exact MvPolynomial.degreeOf_le_totalDegree f 0

/-- **One elimination step for a system of equations.**  Eliminating the first variable against a
distinguished member turns `N + 1` equations of total degree `d` in `m + 1` variables into `N`
equations of total degree `d²` in `m` variables, still vanishing on every projection of a common
zero. -/
theorem exists_eliminated_system {N : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin (m + 1)) K)
    {d : ℕ} (hd : ∀ k, (F k).totalDegree ≤ d) (hdpos : d ≠ 0)
    (hres : ∀ k : Fin N, Polynomial.resultant (MvPolynomial.finSuccEquiv K m (F 0))
      (MvPolynomial.finSuccEquiv K m (F k.succ)) d d ≠ 0) :
    ∃ G : Fin N → MvPolynomial (Fin m) K,
      (∀ k, G k ≠ 0) ∧ (∀ k, (G k).totalDegree ≤ d * d) ∧
      ∀ (s : Fin m → K) (y : K), (∀ k, MvPolynomial.eval (Fin.cons y s) (F k) = 0) →
        ∀ k, MvPolynomial.eval s (G k) = 0 := by
  refine ⟨fun k => Polynomial.resultant (MvPolynomial.finSuccEquiv K m (F 0))
    (MvPolynomial.finSuccEquiv K m (F k.succ)) d d, hres, fun k => ?_, fun s y hzero k => ?_⟩
  · show (Polynomial.resultant (MvPolynomial.finSuccEquiv K m (F 0))
      (MvPolynomial.finSuccEquiv K m (F k.succ)) d d).totalDegree ≤ d * d
    rcases totalDegree_resultant_finSuccEquiv_add_le (hd 0) (hd k.succ) d d with h | h
    · exact absurd h (hres k)
    · omega
  · refine eval_resultant_eq_zero_of_mv_common_zero (F 0) (F k.succ)
      (le_trans (natDegree_finSuccEquiv_le_totalDegree (F 0)) (hd 0))
      (le_trans (natDegree_finSuccEquiv_le_totalDegree (F k.succ)) (hd k.succ))
      (Or.inl hdpos) s y (hzero 0) (hzero k.succ)

end System


/-! ## The elimination tower -/

section Tower

/-- One elimination step, as a system. -/
noncomputable def elimStep (d : ℕ) {N m : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin (m + 1)) K) :
    Fin N → MvPolynomial (Fin m) K :=
  fun k => Polynomial.resultant (MvPolynomial.finSuccEquiv K m (F 0))
    (MvPolynomial.finSuccEquiv K m (F k.succ)) d d

theorem totalDegree_elimStep_le {N m d : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin (m + 1)) K)
    (hd : ∀ i, (F i).totalDegree ≤ d) (k : Fin N) :
    (elimStep d F k).totalDegree ≤ d * d := by
  rcases totalDegree_resultant_finSuccEquiv_add_le (hd 0) (hd k.succ) d d with h | h
  · rw [elimStep, h, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · rw [elimStep]
    omega

theorem eval_elimStep_eq_zero {N m d : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin (m + 1)) K)
    (hd : ∀ i, (F i).totalDegree ≤ d) (hdpos : d ≠ 0) (x : Fin (m + 1) → K)
    (hzero : ∀ i, MvPolynomial.eval x (F i) = 0) (k : Fin N) :
    MvPolynomial.eval (Fin.tail x) (elimStep d F k) = 0 := by
  have hx : Fin.cons (x 0) (Fin.tail x) = x := Fin.cons_self_tail x
  refine eval_resultant_eq_zero_of_mv_common_zero (F 0) (F k.succ)
    (le_trans (natDegree_finSuccEquiv_le_totalDegree (F 0)) (hd 0))
    (le_trans (natDegree_finSuccEquiv_le_totalDegree (F k.succ)) (hd k.succ))
    (Or.inl hdpos) (Fin.tail x) (x 0) ?_ ?_
  · rw [hx]; exact hzero 0
  · rw [hx]; exact hzero k.succ

/-- **The elimination tower**: repeated elimination of the leading variable from a square system,
ending in a single polynomial in one variable. -/
noncomputable def elimTower : (k : ℕ) → (Fin (k + 1) → MvPolynomial (Fin (k + 1)) K) → ℕ →
    MvPolynomial (Fin 1) K
  | 0, F, _ => F 0
  | (k + 1), F, d => elimTower k (elimStep d F) (d * d)

theorem totalDegree_elimTower_le : ∀ (k : ℕ) (F : Fin (k + 1) → MvPolynomial (Fin (k + 1)) K)
    (d : ℕ), (∀ i, (F i).totalDegree ≤ d) → (elimTower k F d).totalDegree ≤ d ^ (2 ^ k)
  | 0, F, d, hd => by
    rw [elimTower, pow_zero, pow_one]
    exact hd 0
  | (k + 1), F, d, hd => by
    rw [elimTower]
    have := totalDegree_elimTower_le k (elimStep d F) (d * d)
      (totalDegree_elimStep_le F hd)
    calc (elimTower k (elimStep d F) (d * d)).totalDegree ≤ (d * d) ^ (2 ^ k) := this
      _ = d ^ (2 ^ (k + 1)) := by
          rw [← pow_two d, ← pow_mul, pow_succ, mul_comm (2 ^ k) 2]

/-- **The tower vanishes at the last coordinate of every common zero.** -/
theorem eval_elimTower_eq_zero : ∀ (k : ℕ) (F : Fin (k + 1) → MvPolynomial (Fin (k + 1)) K)
    (d : ℕ), d ≠ 0 → (∀ i, (F i).totalDegree ≤ d) →
    ∀ x : Fin (k + 1) → K, (∀ i, MvPolynomial.eval x (F i) = 0) →
      MvPolynomial.eval (fun i : Fin 1 => x (Fin.natAdd k i)) (elimTower k F d) = 0
  | 0, F, d, _, _, x, hzero => by
    rw [elimTower]
    have hpt : (fun i : Fin 1 => x (Fin.natAdd 0 i)) = x := by
      funext i
      congr 1
      exact Fin.ext (by simp)
    rw [hpt]
    exact hzero 0
  | (k + 1), F, d, hdpos, hd, x, hzero => by
    rw [elimTower]
    have hstep := eval_elimTower_eq_zero k (elimStep d F) (d * d)
      (mul_ne_zero hdpos hdpos) (totalDegree_elimStep_le F hd) (Fin.tail x)
      (eval_elimStep_eq_zero F hd hdpos x hzero)
    have hpt : (fun i : Fin 1 => Fin.tail x (Fin.natAdd k i))
        = fun i : Fin 1 => x (Fin.natAdd (k + 1) i) := by
      funext i
      rw [Fin.tail]
      congr 1
      exact Fin.ext (by simp)
    rwa [hpt] at hstep

end Tower


/-! ## Counting the last coordinate -/

section Count

variable [IsDomain K]

omit [IsDomain K] in
/-- The evaluation of a polynomial with no variables is injective. -/
theorem eval_empty_injective :
    Function.Injective (MvPolynomial.eval (fun _ : Fin 0 => (0 : K))) := by
  have hext : (MvPolynomial.eval (fun _ : Fin 0 => (0 : K))
      : MvPolynomial (Fin 0) K →+* K)
      = ((MvPolynomial.isEmptyRingEquiv K (Fin 0) : MvPolynomial (Fin 0) K ≃+* K)
        : MvPolynomial (Fin 0) K →+* K) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => i.elim0)
    rw [MvPolynomial.eval_C]
    exact (MvPolynomial.coeff_zero_C r).symm
  rw [show (MvPolynomial.eval (fun _ : Fin 0 => (0 : K)))
      = ⇑((MvPolynomial.isEmptyRingEquiv K (Fin 0) : MvPolynomial (Fin 0) K ≃+* K)) from
    congrArg (fun f : MvPolynomial (Fin 0) K →+* K => ⇑f) hext]
  exact (MvPolynomial.isEmptyRingEquiv K (Fin 0)).injective

/-- **A nonzero polynomial in one variable has at most its total degree many roots.** -/
theorem card_roots_mvPolynomial_one_le {G : MvPolynomial (Fin 1) K} (hG : G ≠ 0)
    (s : Finset K) (hs : ∀ y ∈ s, MvPolynomial.eval (fun _ => y) G = 0) :
    s.card ≤ G.totalDegree := by
  classical
  set g : K[X] := (MvPolynomial.finSuccEquiv K 0 G).map
    (MvPolynomial.eval (fun _ : Fin 0 => (0 : K))) with hg
  have hg0 : g ≠ 0 := by
    intro h0
    refine hG ?_
    have hmap := Polynomial.map_injective
      (MvPolynomial.eval (fun _ : Fin 0 => (0 : K))) eval_empty_injective
    have : MvPolynomial.finSuccEquiv K 0 G = 0 := by
      refine hmap ?_
      rw [← hg, h0, Polynomial.map_zero]
    exact (MvPolynomial.finSuccEquiv K 0).injective (by rw [this, map_zero])
  have hdeg : g.natDegree ≤ G.totalDegree :=
    le_trans (Polynomial.natDegree_map_le) (natDegree_finSuccEquiv_le_totalDegree G)
  have hroot : ∀ y ∈ s, g.IsRoot y := by
    intro y hy
    have hpt : (fun _ : Fin 1 => y) = Fin.cons y (fun _ : Fin 0 => (0 : K)) := by
      funext i
      refine (Fin.cases ?_ (fun j => j.elim0) i)
      rfl
    have := hs y hy
    rw [hpt, MvPolynomial.eval_eq_eval_mv_eval'] at this
    exact this
  have hsub : s ⊆ g.roots.toFinset := fun y hy =>
    Multiset.mem_toFinset.2 ((Polynomial.mem_roots hg0).2 (hroot y hy))
  calc s.card ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' _
    _ ≤ G.totalDegree := hdeg

/-- **The last coordinate of a common zero of a square system takes at most `d^(2^k)` values.** -/
theorem card_last_coord_le {k : ℕ} (F : Fin (k + 1) → MvPolynomial (Fin (k + 1)) K) (d : ℕ)
    (hdpos : d ≠ 0) (hd : ∀ i, (F i).totalDegree ≤ d) (htower : elimTower k F d ≠ 0)
    (s : Finset K)
    (hs : ∀ y ∈ s, ∃ x : Fin (k + 1) → K, x (Fin.last k) = y ∧
      ∀ i, MvPolynomial.eval x (F i) = 0) :
    s.card ≤ d ^ (2 ^ k) := by
  refine le_trans (card_roots_mvPolynomial_one_le htower s fun y hy => ?_)
    (totalDegree_elimTower_le k F d hd)
  obtain ⟨x, hx, hzero⟩ := hs y hy
  have hpt : (fun i : Fin 1 => x (Fin.natAdd k i)) = fun _ : Fin 1 => y := by
    funext i
    rw [← hx]
    congr 1
    exact Fin.ext (by simp)
  rw [← hpt]
  exact eval_elimTower_eq_zero k F d hdpos hd x hzero


/-- **The roots of a nonzero polynomial in one variable, as a finite set.** -/
theorem exists_finset_roots_mvPolynomial_one {G : MvPolynomial (Fin 1) K} (hG : G ≠ 0) :
    ∃ s : Finset K, s.card ≤ G.totalDegree ∧
      ∀ y : K, MvPolynomial.eval (fun _ => y) G = 0 → y ∈ s := by
  classical
  set g : K[X] := (MvPolynomial.finSuccEquiv K 0 G).map
    (MvPolynomial.eval (fun _ : Fin 0 => (0 : K))) with hg
  have hg0 : g ≠ 0 := by
    intro h0
    refine hG ?_
    have hmap := Polynomial.map_injective
      (MvPolynomial.eval (fun _ : Fin 0 => (0 : K))) eval_empty_injective
    have hz : MvPolynomial.finSuccEquiv K 0 G = 0 := by
      refine hmap ?_
      rw [← hg, h0, Polynomial.map_zero]
    exact (MvPolynomial.finSuccEquiv K 0).injective (by rw [hz, map_zero])
  refine ⟨g.roots.toFinset, ?_, fun y hy => ?_⟩
  · calc g.roots.toFinset.card ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := Polynomial.card_roots' _
      _ ≤ G.totalDegree :=
        le_trans (Polynomial.natDegree_map_le) (natDegree_finSuccEquiv_le_totalDegree G)
  · refine Multiset.mem_toFinset.2 ((Polynomial.mem_roots hg0).2 ?_)
    have hpt : (fun _ : Fin 1 => y) = Fin.cons y (fun _ : Fin 0 => (0 : K)) := by
      funext i
      refine (Fin.cases ?_ (fun j => j.elim0) i)
      rfl
    rw [hpt, MvPolynomial.eval_eq_eval_mv_eval'] at hy
    exact hy

/-- **The last coordinates of the common zeros of a square system, as a finite set.** -/
theorem exists_finset_last_coord {k : ℕ} (F : Fin (k + 1) → MvPolynomial (Fin (k + 1)) K) (d : ℕ)
    (hdpos : d ≠ 0) (hd : ∀ i, (F i).totalDegree ≤ d) (htower : elimTower k F d ≠ 0) :
    ∃ s : Finset K, s.card ≤ d ^ (2 ^ k) ∧
      ∀ x : Fin (k + 1) → K, (∀ i, MvPolynomial.eval x (F i) = 0) → x (Fin.last k) ∈ s := by
  obtain ⟨s, hcard, hmem⟩ := exists_finset_roots_mvPolynomial_one htower
  refine ⟨s, le_trans hcard (totalDegree_elimTower_le k F d hd), fun x hzero => ?_⟩
  refine hmem (x (Fin.last k)) ?_
  have hpt : (fun i : Fin 1 => x (Fin.natAdd k i)) = fun _ : Fin 1 => x (Fin.last k) := by
    funext i
    congr 1
    exact Fin.ext (by simp)
  rw [← hpt]
  exact eval_elimTower_eq_zero k F d hdpos hd x hzero

end Count

end GaloisForLFunctions.HTGeometry
