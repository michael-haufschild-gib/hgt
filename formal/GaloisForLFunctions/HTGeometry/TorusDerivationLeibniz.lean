import GaloisForLFunctions.HTGeometry.PhaseJetRelationTransfer

/-!
# The torus derivation is a derivation, and the jet chain rule

`δ = Σ_j i ω_j z_j ∂_j` is additive, kills constants and obeys the Leibniz
rule on the functions holomorphic on an open set.  Consequently it acts on a
polynomial expression in holomorphic functions by the chain rule, through the
partial derivatives of the polynomial.

Applied to a polynomial relation among the phase jets, and using that the
derivation shifts the jet index, this is the differentiated relation used to
solve for the next jet.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Leibniz rules for the coordinate derivatives -/

theorem coordDeriv_add {U : Set (d → ℂ)} {F G : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) (j : d)
    {z : d → ℂ} (hz : z ∈ U) :
    coordDeriv (fun w => F w + G w) j z = coordDeriv F j z + coordDeriv G j z := by
  have hFd : HasFDerivAt F (fderiv ℂ F z) z := (hF z hz).differentiableAt.hasFDerivAt
  have hGd : HasFDerivAt G (fderiv ℂ G z) z := (hG z hz).differentiableAt.hasFDerivAt
  have hsum : HasFDerivAt (fun w => F w + G w) (fderiv ℂ F z + fderiv ℂ G z) z :=
    hFd.add hGd
  rw [coordDeriv, hsum.fderiv]
  rfl

theorem coordDeriv_mul {U : Set (d → ℂ)} {F G : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) (j : d)
    {z : d → ℂ} (hz : z ∈ U) :
    coordDeriv (fun w => F w * G w) j z
      = F z * coordDeriv G j z + G z * coordDeriv F j z := by
  have hFd : HasFDerivAt F (fderiv ℂ F z) z := (hF z hz).differentiableAt.hasFDerivAt
  have hGd : HasFDerivAt G (fderiv ℂ G z) z := (hG z hz).differentiableAt.hasFDerivAt
  have hmul : HasFDerivAt (fun w => F w * G w)
      (F z • fderiv ℂ G z + G z • fderiv ℂ F z) z := hFd.mul hGd
  rw [coordDeriv, hmul.fderiv]
  rfl

omit [Fintype d] in
theorem coordDeriv_const (c : ℂ) (j : d) (z : d → ℂ) :
    coordDeriv (fun _ : d → ℂ => c) j z = 0 := by
  rw [coordDeriv]
  simp

/-! ### Leibniz rules for the torus derivation -/

theorem torusDerivation_add {U : Set (d → ℂ)} (omega : d → ℝ)
    {F G : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    {z : d → ℂ} (hz : z ∈ U) :
    torusDerivation omega (fun w => F w + G w) z
      = torusDerivation omega F z + torusDerivation omega G z := by
  rw [torusDerivation, torusDerivation, torusDerivation, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordDeriv_add hF hG j hz]
  ring

theorem torusDerivation_mul {U : Set (d → ℂ)} (omega : d → ℝ)
    {F G : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    {z : d → ℂ} (hz : z ∈ U) :
    torusDerivation omega (fun w => F w * G w) z
      = F z * torusDerivation omega G z + G z * torusDerivation omega F z := by
  rw [torusDerivation, torusDerivation, torusDerivation, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordDeriv_mul hF hG j hz]
  ring

theorem torusDerivation_const (omega : d → ℝ) (c : ℂ) (z : d → ℂ) :
    torusDerivation omega (fun _ : d → ℂ => c) z = 0 := by
  rw [torusDerivation]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coordDeriv_const, mul_zero]

/-! ### The polynomial chain rule -/

/-- **The chain rule for the torus derivation.**  A polynomial expression in
holomorphic functions is differentiated through the partial derivatives of the
polynomial. -/
theorem torusDerivation_eval_mvPolynomial {σ : Type} [Fintype σ] [DecidableEq σ]
    {U : Set (d → ℂ)} (omega : d → ℝ) {g : σ → (d → ℂ) → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) (Q : MvPolynomial σ ℂ)
    {z : d → ℂ} (hz : z ∈ U) :
    torusDerivation omega (fun w => MvPolynomial.eval (fun i => g i w) Q) z
      = ∑ i : σ, MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i Q)
          * torusDerivation omega (g i) z := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun w : d → ℂ =>
          MvPolynomial.eval (fun i => g i w) (MvPolynomial.C a)) = fun _ => a := by
        funext w
        rw [MvPolynomial.eval_C]
      rw [hfun, torusDerivation_const]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [MvPolynomial.pderiv_C, map_zero, zero_mul]
  | add p q hp hq =>
      have hfun : (fun w : d → ℂ =>
            MvPolynomial.eval (fun i => g i w) (p + q)) =
          fun w => MvPolynomial.eval (fun i => g i w) p +
            MvPolynomial.eval (fun i => g i w) q := by
        funext w
        rw [map_add]
      rw [hfun, torusDerivation_add omega (analyticOnNhd_mvPolynomialEval hg p)
        (analyticOnNhd_mvPolynomialEval hg q) hz, hp, hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, map_add]
      ring
  | mul_X p j hp =>
      have hfun : (fun w : d → ℂ =>
            MvPolynomial.eval (fun i => g i w) (p * MvPolynomial.X j)) =
          fun w => MvPolynomial.eval (fun i => g i w) p * g j w := by
        funext w
        rw [map_mul, MvPolynomial.eval_X]
      have hpd : ∀ i : σ,
          MvPolynomial.eval (fun i => g i z)
              (MvPolynomial.pderiv i (p * MvPolynomial.X j))
            = MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i p) * g j z
              + MvPolynomial.eval (fun i => g i z) p * (if j = i then 1 else 0) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul,
          map_mul, MvPolynomial.pderiv_X, MvPolynomial.eval_X, Pi.single_apply]
        by_cases hij : j = i
        · simp only [if_pos hij, map_one]
          ring
        · simp only [if_neg hij, map_zero]
          ring
      have hterm : ∀ i : σ, MvPolynomial.eval (fun i => g i z)
            (MvPolynomial.pderiv i (p * MvPolynomial.X j)) *
              torusDerivation omega (g i) z
          = g j z * (MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i p)
              * torusDerivation omega (g i) z)
            + (if j = i then MvPolynomial.eval (fun i => g i z) p
                * torusDerivation omega (g i) z else 0) := by
        intro i
        rw [hpd i]
        by_cases hij : j = i
        · rw [if_pos hij, if_pos hij]
          ring
        · rw [if_neg hij, if_neg hij]
          ring
      rw [hfun, torusDerivation_mul omega (analyticOnNhd_mvPolynomialEval hg p)
        (hg j) hz, hp]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        ← Finset.mul_sum,
        Finset.sum_ite_eq Finset.univ j (fun i => MvPolynomial.eval (fun i => g i z) p
          * torusDerivation omega (g i) z), if_pos (Finset.mem_univ j)]
      ring

/-! ### Differentiating a relation among the phase jets -/

theorem torusDerivation_phaseJet (omega : d → ℝ) (F : (d → ℂ) → ℂ) (k : ℕ) :
    torusDerivation omega (phaseJet omega F k) = phaseJet omega F (k + 1) := by
  rw [phaseJet, phaseJet, Function.iterate_succ_apply']

/-- Evaluation of a polynomial relation among the first `N` phase jets. -/
def jetRelationEval (omega : d → ℝ) (F : (d → ℂ) → ℂ) {N : ℕ}
    (Q : MvPolynomial (Fin N) ℂ) (z : d → ℂ) : ℂ :=
  MvPolynomial.eval (fun i : Fin N => phaseJet omega F (i : ℕ) z) Q

theorem analyticOnNhd_jetRelationEval {U : Set (d → ℂ)} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) {N : ℕ}
    (Q : MvPolynomial (Fin N) ℂ) :
    AnalyticOnNhd ℂ (jetRelationEval omega F Q) U :=
  analyticOnNhd_mvPolynomialEval
    (g := fun i : Fin N => phaseJet omega F (i : ℕ))
    (fun i => analyticOnNhd_phaseJet omega hF (i : ℕ)) Q

/-- **Equation `(14)`: differentiating a jet relation shifts every jet
index.** -/
theorem torusDerivation_jetRelationEval {U : Set (d → ℂ)} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F U) {N : ℕ}
    (Q : MvPolynomial (Fin N) ℂ) {z : d → ℂ} (hz : z ∈ U) :
    torusDerivation omega (jetRelationEval omega F Q) z
      = ∑ i : Fin N,
          MvPolynomial.eval (fun j : Fin N => phaseJet omega F (j : ℕ) z)
            (MvPolynomial.pderiv i Q) * phaseJet omega F ((i : ℕ) + 1) z := by
  have hchain := torusDerivation_eval_mvPolynomial (σ := Fin N) omega
    (g := fun i : Fin N => phaseJet omega F (i : ℕ))
    (fun i => analyticOnNhd_phaseJet omega hF (i : ℕ)) Q hz
  have heq : jetRelationEval omega F Q
      = fun w => MvPolynomial.eval (fun i : Fin N => phaseJet omega F (i : ℕ) w) Q := rfl
  rw [heq, hchain]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [torusDerivation_phaseJet]

end

end GaloisForLFunctions.HTGeometry
