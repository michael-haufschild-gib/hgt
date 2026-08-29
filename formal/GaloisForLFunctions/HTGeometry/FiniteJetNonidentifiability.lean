import GaloisForLFunctions.HTGeometry.AsymptoticFlatHypertranscendentalInvisibility
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicCancellation
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence

/-!
# Finite jets cannot identify hypertranscendence

Every prescribed finite jet table at finitely many distinct points is realized simultaneously by a
polynomial — differentially algebraic — and by a punctured affine line of entire
hypertranscendental functions `P + λ·A/Γ`, where `A` is the modulus vanishing to the prescribed
order at every node.  Hence no finite jet observation can decide differential algebraicity.

* `gammaPerturbation` — the entire perturbation `λ·A(z)/Γ(z)`.
* `hypertranscendental_gammaPerturbation` — it is hypertranscendental for `λ ≠ 0`, `A ≠ 0`.
* `exists_multipoint_finiteJet_da_and_ht` — the multi-point finite-jet two-realization theorem.
* `da_ht_invisible_perturbation_on` — the invisible-perturbation strengthening on a domain.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

noncomputable section

/-- Every polynomial function is differentially algebraic. -/
theorem differentiallyAlgebraic_polynomial (B : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun z => B.eval z) := by
  refine differentiallyAlgebraic_of_iteratedDeriv_eq_zero (m := B.natDegree + 1) fun z => ?_
  rw [iteratedDeriv_polynomial_eval,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)]
  simp

/-- The entire perturbation `λ·A(z)/Γ(z)`. -/
def gammaPerturbation (lam : ℂ) (A : Polynomial ℂ) : ℂ → ℂ :=
  fun z => lam * A.eval z * (Complex.Gamma z)⁻¹

theorem differentiable_invGamma : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
  Complex.differentiable_one_div_Gamma

theorem differentiable_gammaPerturbation (lam : ℂ) (A : Polynomial ℂ) :
    Differentiable ℂ (gammaPerturbation lam A) :=
  ((differentiable_const lam).mul (A.differentiable)).mul differentiable_invGamma

theorem analyticOnNhd_gammaPerturbation (lam : ℂ) (A : Polynomial ℂ) :
    AnalyticOnNhd ℂ (gammaPerturbation lam A) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.2 (differentiable_gammaPerturbation lam A)

/-- **The perturbation is hypertranscendental.**  Dividing back by the nonzero polynomial
multiplier would make `1/Γ` differentially algebraic, contradicting Hölder's theorem. -/
theorem hypertranscendental_gammaPerturbation {lam : ℂ} (hlam : lam ≠ 0)
    {A : Polynomial ℂ} (hA : A ≠ 0) : Hypertranscendental (gammaPerturbation lam A) := by
  intro hDA
  refine hypertranscendental_invGamma ?_
  set B : Polynomial ℂ := Polynomial.C lam * A with hBdef
  have hBne : B ≠ 0 := mul_ne_zero (by simpa using hlam) hA
  have hBan : AnalyticOnNhd ℂ (fun z => B.eval z) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 B.differentiable
  have hinvan : AnalyticOnNhd ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 differentiable_invGamma
  have hrel : ∀ z : ℂ, B.eval z * (Complex.Gamma z)⁻¹ = gammaPerturbation lam A z := by
    intro z
    rw [hBdef, gammaPerturbation, Polynomial.eval_mul, Polynomial.eval_C]
  have hBnz : ∃ z : ℂ, B.eval z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hBne (Polynomial.funext (fun z => by simpa using hcon z))
  exact differentiallyAlgebraic_right_of_mul_eq hBan hinvan
    (analyticOnNhd_gammaPerturbation lam A) hBnz hrel (differentiallyAlgebraic_polynomial B) hDA

/-- The perturbation has vanishing jets to the prescribed order at every node. -/
theorem iteratedDeriv_gammaPerturbation_jetModulus_eq_zero {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (m : ι → ℕ) (lam : ℂ) (i : ι) {n : ℕ} (hn : n ≤ m i) :
    iteratedDeriv n (gammaPerturbation lam (jetModulus a m)) (a i) = 0 := by
  have hinvG : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => (Complex.Gamma z)⁻¹ :=
    differentiable_invGamma.contDiff
  have hAcd : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => lam * (jetModulus a m).eval z :=
    contDiff_const.mul ((Polynomial.differentiable (jetModulus a m)).contDiff)
  have hjets : ∀ l, l ≤ m i →
      iteratedDeriv l (fun z : ℂ => lam * (jetModulus a m).eval z) (a i)
        = iteratedDeriv l (fun _ : ℂ => (0 : ℂ)) (a i) := by
    intro l hl
    have hpoly : ContDiffAt ℂ ((l : ℕ) : ℕ∞) (fun z : ℂ => (jetModulus a m).eval z) (a i) :=
      ((Polynomial.differentiable (jetModulus a m)).contDiff (n := ((l : ℕ) : ℕ∞))).contDiffAt
    rw [iteratedDeriv_const_mul (f := fun z : ℂ => (jetModulus a m).eval z) lam hpoly,
      iteratedDeriv_jetModulus_eq_zero a m i hl, mul_zero, iteratedDeriv_const]
    simp
  have hcongr := iteratedDeriv_mul_jet_congr
    (f := fun z : ℂ => lam * (jetModulus a m).eval z) (g := fun _ : ℂ => (0 : ℂ))
    (h := fun z : ℂ => (Complex.Gamma z)⁻¹) (a := a i) (m := m i)
    hAcd.contDiffAt contDiff_const.contDiffAt hinvG.contDiffAt hjets hn
  have hswap : gammaPerturbation lam (jetModulus a m)
      = fun z : ℂ => (Complex.Gamma z)⁻¹ * (lam * (jetModulus a m).eval z) := by
    funext z
    rw [gammaPerturbation]
    ring
  rw [hswap, hcongr]
  simp

/-- Adding the perturbation does not change any jet up to the prescribed order. -/
theorem iteratedDeriv_add_gammaPerturbation {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (m : ι → ℕ) (lam : ℂ) {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (i : ι) {n : ℕ} (hn : n ≤ m i) :
    iteratedDeriv n (fun z => G z + gammaPerturbation lam (jetModulus a m) z) (a i)
      = iteratedDeriv n G (a i) := by
  have hGcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) G (a i) :=
    (hG.contDiff (n := ((n : ℕ) : ℕ∞))).contDiffAt
  have hPcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) (gammaPerturbation lam (jetModulus a m)) (a i) :=
    ((differentiable_gammaPerturbation lam (jetModulus a m)).contDiff
      (n := ((n : ℕ) : ℕ∞))).contDiffAt
  have hsum : (fun z => G z + gammaPerturbation lam (jetModulus a m) z)
      = G + gammaPerturbation lam (jetModulus a m) := rfl
  rw [hsum, iteratedDeriv_add hGcd hPcd,
    iteratedDeriv_gammaPerturbation_jetModulus_eq_zero a m lam i hn, add_zero]


/-! ## The multi-point finite-jet two-realization theorem -/

/-- **Theorem: multi-point finite-jet indistinguishability.**  Fix distinct nodes `a i`, orders
`m i` and arbitrary complex jet values `c i n`.  There is a polynomial realizing the jet table —
hence differentially algebraic — and, for every `λ ≠ 0`, an *entire hypertranscendental* function
`P + λ·A/Γ` realizing exactly the same jet table, where `A` is the modulus with a zero of order
`m i + 1` at every node.  Finite jets therefore cannot decide differential algebraicity. -/
theorem exists_multipoint_finiteJet_da_and_ht {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : Function.Injective a) (m : ι → ℕ) (c : ι → ℕ → ℂ) :
    ∃ P : Polynomial ℂ,
      (∀ i n, n ≤ m i → iteratedDeriv n (fun z => P.eval z) (a i) = c i n) ∧
      DifferentiallyAlgebraic (fun z => P.eval z) ∧
      ∀ lam : ℂ, lam ≠ 0 →
        Differentiable ℂ (fun z => P.eval z + gammaPerturbation lam (jetModulus a m) z) ∧
        (∀ i n, n ≤ m i →
          iteratedDeriv n (fun z => P.eval z + gammaPerturbation lam (jetModulus a m) z) (a i)
            = c i n) ∧
        Hypertranscendental (fun z => P.eval z + gammaPerturbation lam (jetModulus a m) z) := by
  obtain ⟨P, hP⟩ := exists_polynomial_iteratedDeriv_eval_eq a ha m c
  refine ⟨P, hP, differentiallyAlgebraic_polynomial P, fun lam hlam => ?_⟩
  have hpertdiff : Differentiable ℂ (gammaPerturbation lam (jetModulus a m)) :=
    differentiable_gammaPerturbation lam (jetModulus a m)
  refine ⟨(P.differentiable).add hpertdiff, ?_, ?_⟩
  · intro i n hn
    rw [iteratedDeriv_add_gammaPerturbation a m lam P.differentiable i hn]
    exact hP i n hn
  · intro hDA
    have hswap : (fun z => P.eval z + gammaPerturbation lam (jetModulus a m) z)
        = fun w => gammaPerturbation lam (jetModulus a m) w + P.eval w := by
      funext z; ring
    rw [hswap] at hDA
    have hjet1 : ∀ j : ℕ, Differentiable ℂ
        (iteratedDeriv j (gammaPerturbation lam (jetModulus a m))) :=
      fun j => differentiable_iteratedDeriv_of_entire hpertdiff j
    have hjet2 : ∀ (b : Polynomial ℂ) (j : ℕ), Differentiable ℂ
        (iteratedDeriv j fun w => gammaPerturbation lam (jetModulus a m) w + b.eval w) :=
      fun b j => differentiable_iteratedDeriv_of_entire (hpertdiff.add b.differentiable) j
    have hpertDA :=
      (HTGeometry.differentiallyAlgebraic_add_polynomial_iff hjet1 hjet2 P).1 hDA
    exact hypertranscendental_gammaPerturbation hlam (jetModulus_ne_zero a m) hpertDA

/-! ## The invisible-perturbation strengthening on a domain -/

/-- **Invisible hypertranscendental perturbations of a differentially algebraic germ.**  Let `G` be
analytic and differentially algebraic on a domain `U`, let `B` be an analytic, nowhere vanishing,
differentially algebraic multiplier on `U`, and let `A` be the modulus with a zero of order
`m i + 1` at each node `a i ∈ U`.  Then `G + A·B/Γ` has exactly the same jets as `G` at every node
up to the prescribed order, yet satisfies no algebraic differential equation on `U`. -/
theorem not_differentiallyAlgebraicOn_add_jetPerturbation
    {ι : Type*} [Fintype ι] {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {G : ℂ → ℂ} (hGan : AnalyticOnNhd ℂ G U) (hGDA : DifferentiallyAlgebraicOn G U)
    (a : ι → ℂ) (m : ι → ℕ)
    {B : ℂ → ℂ} (hBan : AnalyticOnNhd ℂ B U) (hBne : ∀ z ∈ U, B z ≠ 0)
    (hBDA : DifferentiallyAlgebraicOn B U) :
    ¬ DifferentiallyAlgebraicOn
      (fun z => G z + (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹) U := by
  intro hDA
  have hinvan : AnalyticOnNhd ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) U := fun z _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.2 differentiable_invGamma) z (Set.mem_univ z)
  have hAan : AnalyticOnNhd ℂ (fun z : ℂ => (jetModulus a m).eval z) U := fun z _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.2
      (jetModulus a m).differentiable) z (Set.mem_univ z)
  have hRan : AnalyticOnNhd ℂ
      (fun z => (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹) U := (hAan.mul hBan).mul hinvan
  have hFan : AnalyticOnNhd ℂ
      (fun z => G z + (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹) U := hGan.add hRan
  have hsub := differentiallyAlgebraicOn_sub hUo hUc hUne hUinf hFan hGan hDA hGDA
  have hfun : (fun z => (G z + (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹) - G z)
      = fun z => (jetModulus a m).eval z * (B z * (Complex.Gamma z)⁻¹) := by
    funext z; ring
  rw [hfun] at hsub
  have hcd : ∀ z ∈ U, ContDiffAt ℂ ((⊤ : ℕ∞) : ℕ∞) (fun w : ℂ => B w * (Complex.Gamma w)⁻¹) z := by
    intro z hz
    exact ((hBan z hz).mul (hinvan z hz)).contDiffAt
  have hBinvDA : DifferentiallyAlgebraicOn (fun z => B z * (Complex.Gamma z)⁻¹) U :=
    differentiallyAlgebraicOn_of_mul_polynomial hcd (jetModulus_ne_zero a m) hsub
  exact not_differentiallyAlgebraicOn_mul_invGamma hUo hUc hUne hUinf hBan hBne hBDA hBinvDA

/-- The perturbed germ has exactly the same finite jets as `G` at every node. -/
theorem iteratedDeriv_add_jetPerturbation_eq
    {ι : Type*} [Fintype ι] {U : Set ℂ}
    {G : ℂ → ℂ} (hGan : AnalyticOnNhd ℂ G U)
    (a : ι → ℂ) (haU : ∀ i, a i ∈ U) (m : ι → ℕ)
    {B : ℂ → ℂ} (hBan : AnalyticOnNhd ℂ B U)
    (i : ι) {n : ℕ} (hn : n ≤ m i) :
    iteratedDeriv n (fun z => G z + (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹) (a i)
      = iteratedDeriv n G (a i) := by
  have hinvG : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => (Complex.Gamma z)⁻¹) (a i) :=
    (differentiable_invGamma.contDiff (n := (⊤ : ℕ∞))).contDiffAt
  have hBcd : ContDiffAt ℂ (⊤ : ℕ∞) B (a i) := (hBan (a i) (haU i)).contDiffAt
  have hAcd : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => (jetModulus a m).eval z) (a i) :=
    ((Polynomial.differentiable (jetModulus a m)).contDiff (n := (⊤ : ℕ∞))).contDiffAt
  have hjets : ∀ l, l ≤ m i →
      iteratedDeriv l (fun z : ℂ => (jetModulus a m).eval z) (a i)
        = iteratedDeriv l (fun _ : ℂ => (0 : ℂ)) (a i) := by
    intro l hl
    rw [iteratedDeriv_jetModulus_eq_zero a m i hl, iteratedDeriv_const]
    simp
  have hcongr := iteratedDeriv_mul_jet_congr
    (f := fun z : ℂ => (jetModulus a m).eval z) (g := fun _ : ℂ => (0 : ℂ))
    (h := fun z : ℂ => B z * (Complex.Gamma z)⁻¹) (a := a i) (m := m i)
    hAcd contDiff_const.contDiffAt (hBcd.mul hinvG) hjets hn
  have hswap : (fun z : ℂ => (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹)
      = fun z : ℂ => (B z * (Complex.Gamma z)⁻¹) * (jetModulus a m).eval z := by
    funext z; ring
  have hzero : iteratedDeriv n
      (fun z : ℂ => (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹) (a i) = 0 := by
    rw [hswap, hcongr]; simp
  have hGcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) G (a i) :=
    ((hGan (a i) (haU i)).contDiffAt).of_le (by exact_mod_cast le_top)
  have hRcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞)
      (fun z : ℂ => (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹) (a i) :=
    (((hAcd.mul hBcd).mul hinvG)).of_le (by exact_mod_cast le_top)
  have hsum : (fun z => G z + (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹)
      = G + fun z => (jetModulus a m).eval z * B z * (Complex.Gamma z)⁻¹ := rfl
  rw [hsum, iteratedDeriv_add hGcd hRcd, hzero, add_zero]

end

end GaloisForLFunctions.HTGeometry
