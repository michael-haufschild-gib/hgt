import Mathlib

/-!
# The jets of an exponential composite

The `l`-th derivative of `exp ∘ p` is `exp ∘ p` times a universal polynomial in the derivatives of
`p`, defined by the recursion `B_0 = 1`, `B_(l+1) = D B_l + B_l · X_1`, where `D` is the derivation
of the jet ring sending the `j`-th jet variable to the `(j+1)`-st.

This makes the jet map of an exponential composite explicit, which is what a parametric jet argument
needs: after dividing by the value, the jets of `exp ∘ p` are a polynomial function of the jets
of `p`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every iterated derivative of an entire function is entire. -/
theorem differentiable_iteratedDeriv_of_entire {p : ℂ → ℂ} (hp : Differentiable ℂ p) (j : ℕ) :
    Differentiable ℂ (iteratedDeriv j p) := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
      have hanal : AnalyticOnNhd ℂ (iteratedDeriv j p) Set.univ :=
        ih.differentiableOn.analyticOnNhd isOpen_univ
      have hsucc : iteratedDeriv (j + 1) p = deriv (iteratedDeriv j p) := iteratedDeriv_succ
      rw [hsucc]
      exact fun x => ((hanal.deriv) x (Set.mem_univ x)).differentiableAt

theorem hasDerivAt_iteratedDeriv_of_entire {p : ℂ → ℂ} (hp : Differentiable ℂ p) (j : ℕ) (x : ℂ) :
    HasDerivAt (iteratedDeriv j p) (iteratedDeriv (j + 1) p x) x := by
  have hdd : HasDerivAt (iteratedDeriv j p) (deriv (iteratedDeriv j p) x) x :=
    (differentiable_iteratedDeriv_of_entire hp j x).hasDerivAt
  rwa [← iteratedDeriv_succ] at hdd

/-- The derivation of the jet ring that raises the order of a jet variable. -/
def jetShiftDeriv : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ fun j => MvPolynomial.X (j + 1)

@[simp] theorem jetShiftDeriv_X (j : ℕ) :
    jetShiftDeriv (MvPolynomial.X j) = MvPolynomial.X (j + 1) :=
  MvPolynomial.mkDerivation_X ℂ _ j

theorem jetShiftDeriv_C (a : ℂ) : jetShiftDeriv (MvPolynomial.C a) = 0 := by
  have hC : (MvPolynomial.C a : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) a := rfl
  rw [hC, Derivation.map_algebraMap]

/-- **Differentiating a polynomial in the jets of a function applies the jet shift.** -/
theorem hasDerivAt_eval_jets {p : ℂ → ℂ} (hp : Differentiable ℂ p) (B : MvPolynomial ℕ ℂ) (x : ℂ) :
    HasDerivAt (fun z => MvPolynomial.eval (fun j => iteratedDeriv j p z) B)
      (MvPolynomial.eval (fun j => iteratedDeriv j p x) (jetShiftDeriv B)) x := by
  classical
  induction B using MvPolynomial.induction_on with
  | C a =>
      rw [jetShiftDeriv_C, map_zero]
      simp only [MvPolynomial.eval_C]
      exact hasDerivAt_const x a
  | add P Q hP hQ =>
      simp only [map_add]
      exact hP.add hQ
  | mul_X P j hP =>
      have hjet : HasDerivAt (fun z => iteratedDeriv j p z) (iteratedDeriv (j + 1) p x) x :=
        hasDerivAt_iteratedDeriv_of_entire hp j x
      have hfun : (fun z => MvPolynomial.eval (fun j => iteratedDeriv j p z)
            (P * MvPolynomial.X j))
          = fun z => MvPolynomial.eval (fun j => iteratedDeriv j p z) P * iteratedDeriv j p z := by
        funext z
        rw [map_mul, MvPolynomial.eval_X]
      have hderiv : jetShiftDeriv (P * MvPolynomial.X j)
          = P * MvPolynomial.X (j + 1) + MvPolynomial.X j * jetShiftDeriv P := by
        rw [Derivation.leibniz, jetShiftDeriv_X]
        simp only [smul_eq_mul]
      rw [hfun, hderiv]
      simp only [map_add, map_mul, MvPolynomial.eval_X]
      have hmul := hP.mul hjet
      have heq : MvPolynomial.eval (fun j => iteratedDeriv j p x) P * iteratedDeriv (j + 1) p x
            + iteratedDeriv j p x
              * MvPolynomial.eval (fun j => iteratedDeriv j p x) (jetShiftDeriv P)
          = MvPolynomial.eval (fun j => iteratedDeriv j p x) (jetShiftDeriv P)
              * iteratedDeriv j p x
            + MvPolynomial.eval (fun j => iteratedDeriv j p x) P * iteratedDeriv (j + 1) p x := by
        ring
      rw [heq]
      exact hmul

/-- The universal polynomial expressing the `l`-th jet of an exponential composite. -/
def expJetPoly : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | (l + 1) => jetShiftDeriv (expJetPoly l) + expJetPoly l * MvPolynomial.X 1

@[simp] theorem expJetPoly_zero : expJetPoly 0 = 1 := rfl

theorem expJetPoly_succ (l : ℕ) :
    expJetPoly (l + 1) = jetShiftDeriv (expJetPoly l) + expJetPoly l * MvPolynomial.X 1 := rfl

/-- **The jets of an exponential composite.** -/
theorem iteratedDeriv_exp_comp {p : ℂ → ℂ} (hp : Differentiable ℂ p) (l : ℕ) (x : ℂ) :
    iteratedDeriv l (fun z => Complex.exp (p z)) x
      = Complex.exp (p x) * MvPolynomial.eval (fun j => iteratedDeriv j p x) (expJetPoly l) := by
  induction l generalizing x with
  | zero => simp
  | succ l ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv l (fun z => Complex.exp (p z))
          = fun z => Complex.exp (p z)
            * MvPolynomial.eval (fun j => iteratedDeriv j p z) (expJetPoly l) := by
        funext z
        exact ih z
      rw [hfun]
      have hp1 : HasDerivAt p (iteratedDeriv 1 p x) x := by
        have hdd : HasDerivAt p (deriv p x) x := (hp x).hasDerivAt
        rwa [iteratedDeriv_one]
      have hexp : HasDerivAt (fun z => Complex.exp (p z))
          (Complex.exp (p x) * iteratedDeriv 1 p x) x := hp1.cexp
      have hB := hasDerivAt_eval_jets hp (expJetPoly l) x
      have hmul : HasDerivAt (fun z => Complex.exp (p z)
          * MvPolynomial.eval (fun j => iteratedDeriv j p z) (expJetPoly l))
          (Complex.exp (p x) * iteratedDeriv 1 p x
              * MvPolynomial.eval (fun j => iteratedDeriv j p x) (expJetPoly l)
            + Complex.exp (p x)
              * MvPolynomial.eval (fun j => iteratedDeriv j p x)
                (jetShiftDeriv (expJetPoly l))) x := hexp.mul hB
      rw [hmul.deriv, expJetPoly_succ]
      simp only [map_add, map_mul, MvPolynomial.eval_X]
      ring

/-! ### Triangularity of the exponential jet polynomials -/

/-- The subalgebra generated by the jet variables of order at most `l`. -/
def jetSub (l : ℕ) : Subalgebra ℂ (MvPolynomial ℕ ℂ) :=
  Algebra.adjoin ℂ (MvPolynomial.X '' (Set.Icc 1 l))

theorem X_mem_jetSub {j l : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ l) : MvPolynomial.X j ∈ jetSub l :=
  Algebra.subset_adjoin ⟨j, ⟨h1, h2⟩, rfl⟩

theorem jetSub_mono {l m : ℕ} (h : l ≤ m) : jetSub l ≤ jetSub m := by
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨j, ⟨h1, h2⟩, rfl⟩
  exact ⟨j, ⟨h1, le_trans h2 h⟩, rfl⟩

/-- **The jet shift raises the subalgebra by one level.** -/
theorem jetShiftDeriv_mem_jetSub {l : ℕ} {B : MvPolynomial ℕ ℂ} (hB : B ∈ jetSub l) :
    jetShiftDeriv B ∈ jetSub (l + 1) := by
  induction hB using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨j, ⟨h1, h2⟩, rfl⟩ := hx
      rw [jetShiftDeriv_X]
      exact X_mem_jetSub (by omega) (by omega)
  | algebraMap r =>
      have hC : (algebraMap ℂ (MvPolynomial ℕ ℂ) r) = MvPolynomial.C r := rfl
      rw [hC, jetShiftDeriv_C]
      exact Subalgebra.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Subalgebra.add_mem _ hx hy
  | mul x y hxm hym hx hy =>
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      exact Subalgebra.add_mem _
        (Subalgebra.mul_mem _ (jetSub_mono (by omega) hxm) hy)
        (Subalgebra.mul_mem _ (jetSub_mono (by omega) hym) hx)

/-- **A partial derivative in a variable above the level kills the subalgebra.** -/
theorem pderiv_eq_zero_of_mem_jetSub {l j : ℕ} (hj : l < j) {B : MvPolynomial ℕ ℂ}
    (hB : B ∈ jetSub l) : MvPolynomial.pderiv j B = 0 := by
  induction hB using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, ⟨h1, h2⟩, rfl⟩ := hx
      rw [MvPolynomial.pderiv_X]
      exact Pi.single_eq_of_ne (by omega) _
  | algebraMap r =>
      have hC : (algebraMap ℂ (MvPolynomial ℕ ℂ) r) = MvPolynomial.C r := rfl
      rw [hC, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy =>
      rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy =>
      rw [MvPolynomial.pderiv_mul, hx, hy, mul_zero, zero_mul, add_zero]

/-- **The exponential jet polynomial is the top jet variable plus lower-order terms.** -/
theorem expJetPoly_eq_X_add (l : ℕ) :
    ∃ R ∈ jetSub l, expJetPoly (l + 1) = MvPolynomial.X (l + 1) + R := by
  induction l with
  | zero =>
      refine ⟨0, Subalgebra.zero_mem _, ?_⟩
      have hD : jetShiftDeriv (1 : MvPolynomial ℕ ℂ) = 0 := by
        have h1 : (1 : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) 1 := by simp
        rw [h1, Derivation.map_algebraMap]
      rw [expJetPoly_succ, expJetPoly_zero, hD]
      ring
  | succ l ih =>
      obtain ⟨R, hR, hEq⟩ := ih
      refine ⟨jetShiftDeriv R + (MvPolynomial.X (l + 1) + R) * MvPolynomial.X 1, ?_, ?_⟩
      · refine Subalgebra.add_mem _ (jetShiftDeriv_mem_jetSub hR) ?_
        refine Subalgebra.mul_mem _ ?_ (X_mem_jetSub (by omega) (by omega))
        exact Subalgebra.add_mem _ (X_mem_jetSub (by omega) (by omega))
          (jetSub_mono (by omega) hR)
      · rw [expJetPoly_succ, hEq, map_add, jetShiftDeriv_X]
        ring

theorem pderiv_expJetPoly_self (l : ℕ) :
    MvPolynomial.pderiv (l + 1) (expJetPoly (l + 1)) = 1 := by
  obtain ⟨R, hR, hEq⟩ := expJetPoly_eq_X_add l
  rw [hEq, map_add, pderiv_eq_zero_of_mem_jetSub (by omega) hR, add_zero,
    MvPolynomial.pderiv_X, Pi.single_eq_same]

theorem expJetPoly_mem_jetSub (l : ℕ) : expJetPoly l ∈ jetSub l := by
  cases l with
  | zero =>
      rw [expJetPoly_zero]
      exact Subalgebra.one_mem _
  | succ l =>
      obtain ⟨R, hR, hEq⟩ := expJetPoly_eq_X_add l
      rw [hEq]
      exact Subalgebra.add_mem _ (X_mem_jetSub (by omega) (by omega))
        (jetSub_mono (by omega) hR)

/-- **The jet map of an exponential composite is triangular.** -/
theorem pderiv_expJetPoly_eq_zero {l j : ℕ} (hj : l < j) :
    MvPolynomial.pderiv j (expJetPoly l) = 0 :=
  pderiv_eq_zero_of_mem_jetSub hj (expJetPoly_mem_jetSub l)

end

end GaloisForLFunctions.HTGeometry
