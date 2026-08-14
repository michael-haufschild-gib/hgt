import GaloisForLFunctions.HTGeometry.ExponentialJetElimination
import GaloisForLFunctions.HTGeometry.CompExpDescent

/-!
# Differential algebraicity is preserved by composition with an exponential

If `g` is entire and satisfies an algebraic differential equation, so does `g (exp (a z))`.

The jets of the composite are the transfer matrix applied to the *weighted* jets
`wʲ·g⁽ʲ⁾(w)` at `w = exp (a z)`, and the transfer matrix is invertible.  Substituting its inverse
into the relation for `g` therefore produces a relation between the jets of the composite and the
exponential, except that the weights appear with negative powers of `w`.  Shifting the exponent of
the point variable of each monomial by its jet weight clears them in advance, at the cost of a
single overall factor `w^N`, which is harmless because it is nowhere zero.  The exponential is then
removed by the degree induction of the elimination layer.

* `GaloisForLFunctions.HTGeometry.expJetEquiv`;
* `GaloisForLFunctions.HTGeometry.expWeightShift`;
* `GaloisForLFunctions.HTGeometry.differentiallyAlgebraic_comp_exp`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-! ### The inverse jet transfer -/

/-- The jet transfer as a linear equivalence. -/
def expJetEquiv (a : ℂ) (n : ℕ) (ha : a ≠ 0) : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearEquiv.ofBijective (expJetLinear a n)
    ⟨expJetLinear_injective ha n, expJetLinear_surjective ha n⟩

@[simp] theorem expJetEquiv_apply (a : ℂ) (n : ℕ) (ha : a ≠ 0) (v : Fin (n + 1) → ℂ) :
    expJetEquiv a n ha v = expJetLinear a n v := rfl

/-- The linear form computing one coordinate of the inverse jet transfer. -/
def expJetInvForm (a : ℂ) (n : ℕ) (ha : a ≠ 0) (j : Fin (n + 1)) : MvPolynomial ℕ ℂ :=
  ∑ k : Fin (n + 1), C ((expJetEquiv a n ha).symm (Pi.single k 1) j) * X (k : ℕ)

theorem eval_expJetInvForm (a : ℂ) (n : ℕ) (ha : a ≠ 0) (Y : ℕ → ℂ) (j : Fin (n + 1)) :
    eval Y (expJetInvForm a n ha j)
      = (expJetEquiv a n ha).symm (fun k : Fin (n + 1) => Y (k : ℕ)) j := by
  classical
  have hsingle : ∀ (k : Fin (n + 1)) (c : ℂ),
      (Pi.single k c : Fin (n + 1) → ℂ) = c • Pi.single k 1 := by
    intro k c
    funext i
    by_cases hik : k = i <;> simp [hik]
  have hdecomp : (fun k : Fin (n + 1) => Y (k : ℕ))
      = ∑ k : Fin (n + 1), (Y (k : ℕ)) • (Pi.single k 1 : Fin (n + 1) → ℂ) := by
    have huniv := Finset.univ_sum_single (f := fun k : Fin (n + 1) => Y (k : ℕ))
    rw [← huniv]
    exact Finset.sum_congr rfl fun k _ => hsingle k (Y (k : ℕ))
  have hrhs : (expJetEquiv a n ha).symm (fun k : Fin (n + 1) => Y (k : ℕ)) j
      = ∑ k : Fin (n + 1), Y (k : ℕ) * ((expJetEquiv a n ha).symm (Pi.single k 1) j) := by
    rw [hdecomp, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [map_smul]
      simp [smul_eq_mul]
  rw [hrhs, expJetInvForm, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, eval_C, eval_X]; ring

/-! ### Evaluation of exponential jet polynomials -/

/-- Evaluating an exponential jet polynomial at a value for the exponential variable and a jet
vector. -/
def jetPolyEvalHom (u : ℂ) (Y : ℕ → ℂ) : ExpJetPoly →+* ℂ :=
  (Polynomial.evalRingHom u).comp (Polynomial.mapRingHom (MvPolynomial.eval Y))

theorem expJetEvalHom_eq_jetPolyEvalHom (a : ℂ) (h : ℂ → ℂ) (z : ℂ) :
    expJetEvalHom a h z = jetPolyEvalHom (Complex.exp (a * z)) (jetVector h z) := rfl

/-- The substitution of the inverse transfer into a differential relation. -/
def expJetAlgSubst (a : ℂ) (n : ℕ) (ha : a ≠ 0) :
    MvPolynomial (Fin (n + 2)) ℂ →ₐ[ℂ] ExpJetPoly :=
  MvPolynomial.aeval fun i : Fin (n + 2) =>
    Fin.cases Polynomial.X (fun j : Fin (n + 1) => Polynomial.C (expJetInvForm a n ha j)) i

theorem jetPolyEvalHom_expJetAlgSubst (a : ℂ) (n : ℕ) (ha : a ≠ 0) (u : ℂ) (Y : ℕ → ℂ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    jetPolyEvalHom u Y (expJetAlgSubst a n ha Q)
      = eval (Fin.cons u ((expJetEquiv a n ha).symm (fun k : Fin (n + 1) => Y (k : ℕ)))) Q := by
  have hext :
      (jetPolyEvalHom u Y).comp ((expJetAlgSubst a n ha : MvPolynomial (Fin (n + 2)) ℂ →+* _))
        = (MvPolynomial.eval
            (Fin.cons u ((expJetEquiv a n ha).symm (fun k : Fin (n + 1) => Y (k : ℕ))))) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      simp [jetPolyEvalHom, expJetAlgSubst]
    · intro i
      induction i using Fin.cases with
      | zero => simp [jetPolyEvalHom, expJetAlgSubst]
      | succ j =>
          simp only [RingHom.coe_comp, Function.comp_apply,
            RingHom.coe_coe, expJetAlgSubst, MvPolynomial.aeval_X, Fin.cases_succ,
            MvPolynomial.eval_X, Fin.cons_succ]
          rw [jetPolyEvalHom]
          simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
            Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]
          exact eval_expJetInvForm a n ha Y j
  exact RingHom.congr_fun hext Q

theorem expJetAlgSubst_injective (a : ℂ) (n : ℕ) (ha : a ≠ 0) :
    Function.Injective (expJetAlgSubst a n ha) := by
  classical
  intro Q₁ Q₂ hQ
  have hzero : expJetAlgSubst a n ha (Q₁ - Q₂) = 0 := by rw [map_sub, hQ, sub_self]
  have hQz : Q₁ - Q₂ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    set u : ℂ := x 0 with hu
    set w : Fin (n + 1) → ℂ := fun j => x j.succ with hw
    set Y : ℕ → ℂ := fun k =>
      if hk : k < n + 1 then (expJetEquiv a n ha) w ⟨k, hk⟩ else 0 with hY
    have hYw : (fun k : Fin (n + 1) => Y (k : ℕ)) = (expJetEquiv a n ha) w := by
      funext k
      rw [hY]
      simp only [dif_pos k.isLt]
    have hcons : Fin.cons u ((expJetEquiv a n ha).symm (fun k : Fin (n + 1) => Y (k : ℕ))) = x := by
      rw [hYw, LinearEquiv.symm_apply_apply]
      funext i
      induction i using Fin.cases with
      | zero => rw [Fin.cons_zero, hu]
      | succ j => rw [Fin.cons_succ, hw]
    have := jetPolyEvalHom_expJetAlgSubst a n ha u Y (Q₁ - Q₂)
    rw [hzero, map_zero, hcons] at this
    rw [← this, map_zero]
  have := sub_eq_zero.1 hQz
  exact this

/-! ### Clearing the weights -/

/-- The weight of a jet monomial: the total order of differentiation it records. -/
def expJetWeight (n : ℕ) (α : Fin (n + 2) →₀ ℕ) : ℕ :=
  ∑ j : Fin (n + 1), (j : ℕ) * α j.succ

/-- The exponent shift compensating the jet weight of a monomial. -/
def expShiftExponent (n N : ℕ) (α : Fin (n + 2) →₀ ℕ) : Fin (n + 2) →₀ ℕ :=
  α + Finsupp.single 0 (N - expJetWeight n α)

@[simp] theorem expShiftExponent_succ (n N : ℕ) (α : Fin (n + 2) →₀ ℕ) (j : Fin (n + 1)) :
    expShiftExponent n N α j.succ = α j.succ := by
  rw [expShiftExponent, Finsupp.add_apply, Finsupp.single_apply,
    if_neg (fun hh => (Fin.succ_ne_zero j) hh.symm), add_zero]

@[simp] theorem expShiftExponent_zero (n N : ℕ) (α : Fin (n + 2) →₀ ℕ) :
    expShiftExponent n N α 0 = α 0 + (N - expJetWeight n α) := by
  rw [expShiftExponent, Finsupp.add_apply, Finsupp.single_eq_same]

theorem expShiftExponent_injective (n N : ℕ) : Function.Injective (expShiftExponent n N) := by
  intro α β hab
  have hsucc : ∀ j : Fin (n + 1), α j.succ = β j.succ := by
    intro j
    have hj := congrArg (fun γ : Fin (n + 2) →₀ ℕ => γ j.succ) hab
    simpa using hj
  have hw : expJetWeight n α = expJetWeight n β :=
    Finset.sum_congr rfl fun j _ => by rw [hsucc j]
  have h0 : α 0 = β 0 := by
    have hz := congrArg (fun γ : Fin (n + 2) →₀ ℕ => γ 0) hab
    simp only [expShiftExponent_zero, hw] at hz
    omega
  refine Finsupp.ext fun i => ?_
  induction i using Fin.cases with
  | zero => exact h0
  | succ j => exact hsucc j

/-- Shifting the point exponent of every monomial by its jet weight. -/
def expWeightShift (n N : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) : MvPolynomial (Fin (n + 2)) ℂ :=
  ∑ α ∈ P.support, monomial (expShiftExponent n N α) (P.coeff α)

theorem coeff_expWeightShift (n N : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {α : Fin (n + 2) →₀ ℕ}
    (hα : α ∈ P.support) :
    (expWeightShift n N P).coeff (expShiftExponent n N α) = P.coeff α := by
  classical
  rw [expWeightShift, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro b _ hba
    rw [MvPolynomial.coeff_monomial, if_neg (fun hh => hba (expShiftExponent_injective n N hh))]
  · intro hcon
    exact absurd hα hcon

theorem expWeightShift_ne_zero (n N : ℕ) {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    expWeightShift n N P ≠ 0 := by
  classical
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.2
    (fun hcon => hP (MvPolynomial.support_eq_empty.1 hcon))
  intro h0
  have hcoeff := coeff_expWeightShift n N P hα
  rw [h0, MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.1 hα) hcoeff.symm

/-- **The weight shift clears the negative powers.**  Evaluated on weighted jets, the shifted
polynomial is the original polynomial evaluated on the unweighted jets, times a fixed power of the
point. -/
theorem eval_expWeightShift (n N : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hN : ∀ α ∈ P.support, expJetWeight n α ≤ N) (u : ℂ) (G : Fin (n + 1) → ℂ) :
    eval (Fin.cons u (fun j : Fin (n + 1) => u ^ (j : ℕ) * G j)) (expWeightShift n N P)
      = u ^ N * eval (Fin.cons u G) P := by
  classical
  set v : Fin (n + 2) → ℂ := Fin.cons u (fun j : Fin (n + 1) => u ^ (j : ℕ) * G j) with hv
  set vG : Fin (n + 2) → ℂ := Fin.cons u G with hvG
  have hv0 : v 0 = u := by rw [hv, Fin.cons_zero]
  have hvs : ∀ j : Fin (n + 1), v j.succ = u ^ (j : ℕ) * G j := fun j => by
    rw [hv, Fin.cons_succ]
  have hvG0 : vG 0 = u := by rw [hvG, Fin.cons_zero]
  have hvGs : ∀ j : Fin (n + 1), vG j.succ = G j := fun j => by rw [hvG, Fin.cons_succ]
  have hleft : eval v (expWeightShift n N P)
      = ∑ α ∈ P.support, P.coeff α * ∏ i : Fin (n + 2), v i ^ (expShiftExponent n N α) i := by
    rw [expWeightShift, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.eval_monomial]
    congr 1
    exact Finsupp.prod_fintype _ _ fun i => pow_zero _
  have hright : eval vG P = ∑ α ∈ P.support, P.coeff α * ∏ i : Fin (n + 2), vG i ^ α i :=
    MvPolynomial.eval_eq' _ P
  rw [hleft, hright, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hL : ∏ i : Fin (n + 2), v i ^ (expShiftExponent n N α) i
      = v 0 ^ (expShiftExponent n N α) 0
        * ∏ j : Fin (n + 1), v j.succ ^ (expShiftExponent n N α) j.succ :=
    Fin.prod_univ_succ (fun i : Fin (n + 2) => v i ^ (expShiftExponent n N α) i)
  have hRt : ∏ i : Fin (n + 2), vG i ^ α i
      = vG 0 ^ α 0 * ∏ j : Fin (n + 1), vG j.succ ^ α j.succ :=
    Fin.prod_univ_succ (fun i : Fin (n + 2) => vG i ^ α i)
  have hRs : ∏ j : Fin (n + 1), vG j.succ ^ α j.succ = ∏ j : Fin (n + 1), G j ^ α j.succ :=
    Finset.prod_congr rfl fun j _ => by rw [hvGs j]
  have hsplit : ∏ j : Fin (n + 1), v j.succ ^ (expShiftExponent n N α) j.succ
      = u ^ (expJetWeight n α) * ∏ j : Fin (n + 1), G j ^ α j.succ := by
    have hfac : ∀ j : Fin (n + 1), v j.succ ^ (expShiftExponent n N α) j.succ
        = u ^ ((j : ℕ) * α j.succ) * G j ^ α j.succ := by
      intro j
      rw [expShiftExponent_succ, hvs j, mul_pow, ← pow_mul]
    rw [Finset.prod_congr rfl fun j _ => hfac j, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rfl
  have hwle : expJetWeight n α ≤ N := hN α hα
  have hpow : u ^ (α 0 + (N - expJetWeight n α)) * u ^ (expJetWeight n α)
      = u ^ N * u ^ α 0 := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hL, hRt, hRs, hv0, hvG0, hsplit, expShiftExponent_zero]
  calc P.coeff α * (u ^ (α 0 + (N - expJetWeight n α))
        * (u ^ (expJetWeight n α) * ∏ j : Fin (n + 1), G j ^ α j.succ))
      = P.coeff α * ((u ^ (α 0 + (N - expJetWeight n α)) * u ^ (expJetWeight n α))
        * ∏ j : Fin (n + 1), G j ^ α j.succ) := by ring
    _ = P.coeff α * ((u ^ N * u ^ α 0) * ∏ j : Fin (n + 1), G j ^ α j.succ) := by rw [hpow]
    _ = u ^ N * (P.coeff α * (u ^ α 0 * ∏ j : Fin (n + 1), G j ^ α j.succ)) := by ring

theorem expJetWeight_le (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {α : Fin (n + 2) →₀ ℕ}
    (hα : α ∈ P.support) : expJetWeight n α ≤ n * P.totalDegree := by
  classical
  have hdeg : ∑ i : Fin (n + 2), α i ≤ P.totalDegree := by
    have hsum : (α.sum fun _ e => e) = ∑ i : Fin (n + 2), α i :=
      Finsupp.sum_fintype _ _ fun _ => rfl
    rw [← hsum]
    exact MvPolynomial.le_totalDegree hα
  have hstep : expJetWeight n α ≤ n * ∑ j : Fin (n + 1), α j.succ := by
    rw [expJetWeight, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 j.isLt)
  have hsub : (∑ j : Fin (n + 1), α j.succ) ≤ ∑ i : Fin (n + 2), α i := by
    have hx : ∑ i : Fin (n + 2), α i = α 0 + ∑ j : Fin (n + 1), α j.succ :=
      Fin.sum_univ_succ (fun i : Fin (n + 2) => α i)
    omega
  calc expJetWeight n α ≤ n * ∑ j : Fin (n + 1), α j.succ := hstep
    _ ≤ n * ∑ i : Fin (n + 2), α i := Nat.mul_le_mul_left _ hsub
    _ ≤ n * P.totalDegree := Nat.mul_le_mul_left _ hdeg

/-! ### The forward substitution -/

/-- **Differential algebraicity is preserved by `z ↦ exp (a z)`.** -/
theorem differentiallyAlgebraic_comp_exp {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) {a : ℂ}
    (ha : a ≠ 0) (hDA : DifferentiallyAlgebraic g) :
    DifferentiallyAlgebraic fun z => g (Complex.exp (a * z)) := by
  classical
  obtain ⟨n, P, hP0, hP⟩ := hDA
  set h : ℂ → ℂ := fun z => g (Complex.exp (a * z)) with hhdef
  have hcd : ContDiff ℂ (⊤ : ℕ∞) h := by
    have hinner : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Complex.exp (a * z) :=
      Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    exact hg.comp hinner
  have hh : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m h) := by
    intro m
    exact hcd.differentiable_iteratedDeriv m (by exact_mod_cast ENat.coe_lt_top m)
  set N : ℕ := n * P.totalDegree with hN
  set Ptil : MvPolynomial (Fin (n + 2)) ℂ := expWeightShift n N P with hPtil
  set F : ExpJetPoly := expJetAlgSubst a n ha Ptil with hF
  have hPtil0 : Ptil ≠ 0 := expWeightShift_ne_zero n N hP0
  have hF0 : F ≠ 0 := by
    intro h0
    exact hPtil0 (expJetAlgSubst_injective a n ha (by rw [map_zero, ← hF]; exact h0))
  have hFzero : ∀ z, expJetEvalHom a h z F = 0 := by
    intro z
    set u : ℂ := Complex.exp (a * z) with hu
    have hjets : (expJetEquiv a n ha).symm
          (fun k : Fin (n + 1) => jetVector h z (k : ℕ))
        = fun j : Fin (n + 1) => u ^ (j : ℕ) * iteratedDeriv (j : ℕ) g u := by
      refine (LinearEquiv.symm_apply_eq _).2 ?_
      funext k
      rw [expJetEquiv_apply]
      exact iteratedDeriv_comp_exp_fin hg a n k z
    rw [hF, expJetEvalHom_eq_jetPolyEvalHom, jetPolyEvalHom_expJetAlgSubst, hjets, hPtil,
      eval_expWeightShift n N P (fun α hα => expJetWeight_le n P hα) u
        (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g u)]
    have hPu : eval (Fin.cons u fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g u) P = 0 := hP u
    rw [hPu, mul_zero]
  obtain ⟨c, hc0, hc⟩ := exists_autonomousJet_of_expJetRelation ha hh hF0 hFzero
  set m : ℕ := c.vars.sup id with hm
  set proj : ℕ → Fin (m + 1) := fun k => if hk : k < m + 1 then ⟨k, hk⟩ else 0 with hproj
  set R : MvPolynomial (Fin (m + 1)) ℂ := rename proj c with hR
  have hvars : ∀ i ∈ c.vars, (proj i : ℕ) = i := by
    intro i hi
    have hle : i ≤ m := Finset.le_sup (f := id) hi
    rw [hproj]
    simp only [dif_pos (Nat.lt_succ_of_le hle)]
  have hevalR : ∀ v : Fin (m + 1) → ℂ, eval v R = eval (fun k : ℕ => v (proj k)) c := by
    intro v
    rw [hR, eval_rename]
    rfl
  have hR0 : R ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ : ∃ y : ℕ → ℂ, eval y c ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hc0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
    have hcongr : eval (fun k : ℕ => (fun i : Fin (m + 1) => y (i : ℕ)) (proj k)) c = eval y c := by
      refine eval_congr_vars fun i hi => ?_
      show y ((proj i : Fin (m + 1)) : ℕ) = y i
      rw [hvars i hi]
    rw [h0] at hevalR
    have := hevalR (fun i : Fin (m + 1) => y (i : ℕ))
    rw [map_zero] at this
    exact hy (hcongr ▸ this.symm)
  refine differentiallyAlgebraic_of_autonomousJet (f := h) hR0 fun z => ?_
  rw [hevalR]
  have hcongr : eval (fun k : ℕ =>
      (fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) h z) (proj k)) c
      = eval (jetVector h z) c := by
    refine eval_congr_vars fun i hi => ?_
    show iteratedDeriv ((proj i : Fin (m + 1)) : ℕ) h z = jetVector h z i
    rw [jetVector, hvars i hi]
  rw [hcongr]
  exact hc z

/-- **Hypertranscendence descends through an exponential composite.** -/
theorem hypertranscendental_of_comp_exp {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) {a : ℂ}
    (ha : a ≠ 0) (hHT : Hypertranscendental fun z => g (Complex.exp (a * z))) :
    Hypertranscendental g :=
  fun hDA => hHT (differentiallyAlgebraic_comp_exp hg ha hDA)

end

end GaloisForLFunctions.HTGeometry
