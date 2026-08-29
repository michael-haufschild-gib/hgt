import GaloisForLFunctions.HTGeometry.AsymptoticFlatHypertranscendentalInvisibility
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicCancellation
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.EntireTaylorUniformApproximation

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

/-- **A polynomial plus the perturbation is still hypertranscendental.** -/
theorem hypertranscendental_polynomial_add_gammaPerturbation {lam : ℂ} (hlam : lam ≠ 0)
    {A : Polynomial ℂ} (hA : A ≠ 0) (P : Polynomial ℂ) :
    Hypertranscendental (fun z => P.eval z + gammaPerturbation lam A z) := by
  intro hDA
  have hpertdiff : Differentiable ℂ (gammaPerturbation lam A) :=
    differentiable_gammaPerturbation lam A
  have hswap : (fun z => P.eval z + gammaPerturbation lam A z)
      = fun w => gammaPerturbation lam A w + P.eval w := by
    funext z; ring
  rw [hswap] at hDA
  have hjet1 : ∀ j : ℕ, Differentiable ℂ (iteratedDeriv j (gammaPerturbation lam A)) :=
    fun j => differentiable_iteratedDeriv_of_entire hpertdiff j
  have hjet2 : ∀ (b : Polynomial ℂ) (j : ℕ), Differentiable ℂ
      (iteratedDeriv j fun w => gammaPerturbation lam A w + b.eval w) :=
    fun b j => differentiable_iteratedDeriv_of_entire (hpertdiff.add b.differentiable) j
  exact hypertranscendental_gammaPerturbation hlam hA
    ((HTGeometry.differentiallyAlgebraic_add_polynomial_iff hjet1 hjet2 P).1 hDA)

/-- **The perturbed family is a genuine affine line.**  Distinct parameters give distinct
functions, so each finite-jet fibre contains a punctured affine complex line of
hypertranscendental members. -/
theorem gammaPerturbation_injective {A : Polynomial ℂ} (hA : A ≠ 0) {lam₁ lam₂ : ℂ}
    (hne : lam₁ ≠ lam₂) : gammaPerturbation lam₁ A ≠ gammaPerturbation lam₂ A := by
  intro heq
  have hc : lam₁ - lam₂ ≠ 0 := sub_ne_zero.mpr hne
  have hzero : ∀ z : ℂ, A.eval z * (Complex.Gamma z)⁻¹ = 0 := by
    intro z
    have hval := congrFun heq z
    rw [gammaPerturbation, gammaPerturbation] at hval
    have h2 : (lam₁ - lam₂) * (A.eval z * (Complex.Gamma z)⁻¹) = 0 := by
      linear_combination hval
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hc
    · exact h
  refine hypertranscendental_gammaPerturbation (lam := 1) one_ne_zero hA ?_
  have hfun : gammaPerturbation 1 A = fun _ : ℂ => (0 : ℂ) := by
    funext z
    rw [gammaPerturbation, one_mul]
    exact hzero z
  rw [hfun]
  exact differentiallyAlgebraic_of_iteratedDeriv_eq_zero (m := 0) (fun z => by simp)

/-- The affine family of realizers is injective in its parameter. -/
theorem polynomial_add_gammaPerturbation_injective (P : Polynomial ℂ) {A : Polynomial ℂ}
    (hA : A ≠ 0) {lam₁ lam₂ : ℂ} (hne : lam₁ ≠ lam₂) :
    (fun z => P.eval z + gammaPerturbation lam₁ A z)
      ≠ fun z => P.eval z + gammaPerturbation lam₂ A z := by
  intro heq
  refine gammaPerturbation_injective hA hne ?_
  funext z
  have := congrFun heq z
  linear_combination this

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
  · exact hypertranscendental_polynomial_add_gammaPerturbation hlam (jetModulus_ne_zero a m) P

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


/-! ## Adaptive finite jet-query protocols -/

/-- A deterministic finite jet-query protocol: the next query — a point and a derivative order — is
determined by the answers received so far. -/
abbrev JetQuery : Type := List ℂ → ℂ × ℕ

/-- The transcript of answers after `t` steps of the protocol run against the oracle `f`. -/
def jetRun (query : JetQuery) (f : ℂ → ℂ) : ℕ → List ℂ
  | 0 => []
  | (t + 1) =>
      jetRun query f t ++
        [iteratedDeriv (query (jetRun query f t)).2 f (query (jetRun query f t)).1]

/-- The list of queries issued in the first `t` steps. -/
def jetQueries (query : JetQuery) (f : ℂ → ℂ) : ℕ → List (ℂ × ℕ)
  | 0 => []
  | (t + 1) => jetQueries query f t ++ [query (jetRun query f t)]

/-- **Transcripts agree when the queried jets agree.**  If a second oracle answers every query
issued along the run against `f` in the same way, the entire transcript is identical. -/
theorem jetRun_congr (query : JetQuery) (f h : ℂ → ℂ) :
    ∀ T : ℕ,
      (∀ p ∈ jetQueries query f T, iteratedDeriv p.2 h p.1 = iteratedDeriv p.2 f p.1) →
      jetRun query h T = jetRun query f T := by
  intro T
  induction T with
  | zero => intro _; rfl
  | succ T ih =>
      intro hq
      have hprev : ∀ p ∈ jetQueries query f T,
          iteratedDeriv p.2 h p.1 = iteratedDeriv p.2 f p.1 := by
        intro p hp
        refine hq p ?_
        rw [jetQueries]
        exact List.mem_append_left _ hp
      have hrun := ih hprev
      have hlast : query (jetRun query f T) ∈ jetQueries query f (T + 1) := by
        rw [jetQueries]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hval := hq _ hlast
      show jetRun query h T ++ _ = jetRun query f T ++ _
      rw [hrun, hval]

/-- **Theorem: no adaptive finite jet-query protocol can certify hypertranscendence.**  Every
halting transcript is produced both by a polynomial — differentially algebraic — and by a punctured
affine line of entire hypertranscendental functions. -/
theorem exists_jetRun_da_and_ht (query : JetQuery) (f : ℂ → ℂ) (T : ℕ) :
    ∃ (P A : Polynomial ℂ), A ≠ 0 ∧
      jetRun query (fun z => P.eval z) T = jetRun query f T ∧
      DifferentiallyAlgebraic (fun z => P.eval z) ∧
      ∀ lam : ℂ, lam ≠ 0 →
        jetRun query (fun z => P.eval z + gammaPerturbation lam A z) T = jetRun query f T ∧
        Hypertranscendental (fun z => P.eval z + gammaPerturbation lam A z) := by
  classical
  set pts : Finset ℂ := ((jetQueries query f T).map Prod.fst).toFinset with hptsdef
  set M : ℕ := ((jetQueries query f T).map Prod.snd).sum with hMdef
  have hmem : ∀ p ∈ jetQueries query f T, p.1 ∈ pts ∧ p.2 ≤ M := by
    intro p hp
    refine ⟨?_, ?_⟩
    · rw [hptsdef, List.mem_toFinset]
      exact List.mem_map_of_mem hp
    · rw [hMdef]
      exact List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map_of_mem hp)
  obtain ⟨P, hPjet, hPDA, hrest⟩ :=
    exists_multipoint_finiteJet_da_and_ht (ι := {x // x ∈ pts}) (fun i => (i : ℂ))
      (fun i j hij => Subtype.ext hij) (fun _ => M) (fun i n => iteratedDeriv n f (i : ℂ))
  refine ⟨P, jetModulus (fun i : {x // x ∈ pts} => (i : ℂ)) (fun _ => M),
    jetModulus_ne_zero _ _, ?_, hPDA, fun lam hlam => ?_⟩
  · refine jetRun_congr query f _ T ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hmem p hp
    exact hPjet ⟨p.1, hp1⟩ p.2 hp2
  · obtain ⟨-, hjets, hHT⟩ := hrest lam hlam
    refine ⟨jetRun_congr query f _ T ?_, hHT⟩
    intro p hp
    obtain ⟨hp1, hp2⟩ := hmem p hp
    exact hjets ⟨p.1, hp1⟩ p.2 hp2

/-! ## Finite continuous linear observations -/

/-- Additivity of a finite observation on entire functions. -/
def ObsAdditive {N : ℕ} (L : (ℂ → ℂ) → (Fin N → ℂ)) : Prop :=
  ∀ f g : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ g → L (fun z => f z + g z) = L f + L g

/-- Homogeneity of a finite observation on entire functions. -/
def ObsHomogeneous {N : ℕ} (L : (ℂ → ℂ) → (Fin N → ℂ)) : Prop :=
  ∀ (c : ℂ) (f : ℂ → ℂ), Differentiable ℂ f → L (fun z => c * f z) = c • L f

/-- Continuity of a finite observation for uniform convergence on balls, i.e. for the compact-open
topology of the space of entire functions. -/
def ObsContinuous {N : ℕ} (L : (ℂ → ℂ) → (Fin N → ℂ)) : Prop :=
  ∀ (F : ℕ → ℂ → ℂ) (h : ℂ → ℂ), (∀ n, Differentiable ℂ (F n)) → Differentiable ℂ h →
    (∀ R : ℝ, 0 < R → TendstoUniformlyOn F h Filter.atTop (Metric.closedBall (0 : ℂ) R)) →
    Filter.Tendsto (fun n => L (F n)) Filter.atTop (nhds (L h))

theorem obs_zero {N : ℕ} {L : (ℂ → ℂ) → (Fin N → ℂ)} (hsmul : ObsHomogeneous L) :
    L (fun _ : ℂ => (0 : ℂ)) = 0 := by
  have h := hsmul 0 (fun _ : ℂ => (0 : ℂ)) (differentiable_const 0)
  have hz : (fun z : ℂ => (0 : ℂ) * ((fun _ : ℂ => (0 : ℂ)) z)) = fun _ : ℂ => (0 : ℂ) := by
    funext z; ring
  rw [hz] at h
  simpa using h

theorem obs_finset_sum {N : ℕ} {L : (ℂ → ℂ) → (Fin N → ℂ)}
    (hadd : ObsAdditive L) (hsmul : ObsHomogeneous L)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (F : ι → ℂ → ℂ)
    (hF : ∀ i, Differentiable ℂ (F i)) :
    L (fun z => ∑ i ∈ s, c i * F i z) = ∑ i ∈ s, c i • L (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using obs_zero hsmul
  | insert b s hb ih =>
      have hdiff1 : Differentiable ℂ (fun z => c b * F b z) := (differentiable_const _).mul (hF b)
      have hdiff2 : Differentiable ℂ (fun z => ∑ i ∈ s, c i * F i z) := fun z =>
        DifferentiableAt.fun_sum fun i _ => ((differentiable_const (c i)).mul (hF i)) z
      have hrw : (fun z => ∑ i ∈ insert b s, c i * F i z)
          = fun z => (c b * F b z) + ∑ i ∈ s, c i * F i z := by
        funext z; rw [Finset.sum_insert hb]
      rw [hrw, hadd _ _ hdiff1 hdiff2, hsmul (c b) (F b) (hF b), ih, Finset.sum_insert hb]

/-- **Theorem: finite continuous linear observations cannot certify hypertranscendence.**  For every
continuous linear observation `L : H(ℂ) → ℂ^N` and every entire `g`, there are polynomials `P` and
`Q ≠ 0` with `L P = L g` and `L (Q/Γ) = 0`; so the observation fibre of `L g` contains the
differentially algebraic function `P` and the punctured affine line of hypertranscendental entire
functions `P + λ·Q/Γ`. -/
theorem exists_finiteLinearObservation_da_and_ht {N : ℕ} {L : (ℂ → ℂ) → (Fin N → ℂ)}
    (hadd : ObsAdditive L) (hsmul : ObsHomogeneous L) (hcont : ObsContinuous L)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      L (fun z => P.eval z) = L g ∧
      DifferentiallyAlgebraic (fun z => P.eval z) ∧
      ∀ lam : ℂ, lam ≠ 0 →
        L (fun z => P.eval z + gammaPerturbation lam Q z) = L g ∧
        Hypertranscendental (fun z => P.eval z + gammaPerturbation lam Q z) := by
  classical
  -- the observations of polynomials form a subspace of `ℂ^N`, hence a closed one
  let S : Submodule ℂ (Fin N → ℂ) :=
    { carrier := {v | ∃ P : Polynomial ℂ, v = L (fun z => P.eval z)}
      zero_mem' := ⟨0, by
        have hrw : (fun z : ℂ => (0 : Polynomial ℂ).eval z) = fun _ : ℂ => (0 : ℂ) := by
          funext z; simp
        rw [hrw, obs_zero hsmul]⟩
      add_mem' := by
        rintro v w ⟨P, rfl⟩ ⟨Q, rfl⟩
        refine ⟨P + Q, ?_⟩
        have hrw : (fun z => (P + Q).eval z) = fun z => P.eval z + Q.eval z := by
          funext z; simp
        rw [hrw, hadd _ _ P.differentiable Q.differentiable]
      smul_mem' := by
        rintro c v ⟨P, rfl⟩
        refine ⟨Polynomial.C c * P, ?_⟩
        have hrw : (fun z => (Polynomial.C c * P).eval z) = fun z => c * P.eval z := by
          funext z; simp
        rw [hrw, hsmul c _ P.differentiable] }
  have hSclosed : IsClosed (S : Set (Fin N → ℂ)) := S.closed_of_finiteDimensional
  have hmemclos : L g ∈ closure (S : Set (Fin N → ℂ)) := by
    refine mem_closure_of_tendsto (b := Filter.atTop)
      (f := fun n => L (fun z => (taylorPoly g n).eval z)) ?_ ?_
    · exact hcont (fun n z => (taylorPoly g n).eval z) g
        (fun n => (taylorPoly g n).differentiable) hg
        (fun R hR => tendstoUniformlyOn_taylorPoly hg hR)
    · exact Filter.Eventually.of_forall fun n => ⟨taylorPoly g n, rfl⟩
  rw [hSclosed.closure_eq] at hmemclos
  obtain ⟨P, hP⟩ := hmemclos
  -- a nonzero polynomial in the kernel of `Q ↦ L (Q/Γ)`
  set w : Fin (N + 1) → (Fin N → ℂ) :=
    fun i => L (fun z => z ^ (i : ℕ) * (Complex.Gamma z)⁻¹) with hwdef
  have hnotli : ¬ LinearIndependent ℂ w := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_fin_fun] at hcard
    omega
  obtain ⟨v, hvsum, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hnotli
  set Q : Polynomial ℂ := ∑ i : Fin (N + 1), Polynomial.C (v i) * Polynomial.X ^ (i : ℕ) with hQdef
  have hQcoeff : ∀ j : Fin (N + 1), Q.coeff (j : ℕ) = v j := by
    intro j
    rw [hQdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hbj
      have hne : ¬ ((j : ℕ) = (b : ℕ)) := fun h => hbj (Fin.ext h.symm)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hQne : Q ≠ 0 := by
    intro h
    apply hi0
    rw [← hQcoeff i0, h, Polynomial.coeff_zero]
  have hQeval : ∀ z : ℂ, Q.eval z = ∑ i : Fin (N + 1), v i * z ^ (i : ℕ) := by
    intro z
    rw [hQdef, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hQobs : L (fun z => Q.eval z * (Complex.Gamma z)⁻¹) = 0 := by
    have hrw : (fun z => Q.eval z * (Complex.Gamma z)⁻¹)
        = fun z => ∑ i : Fin (N + 1), v i * (z ^ (i : ℕ) * (Complex.Gamma z)⁻¹) := by
      funext z
      rw [hQeval z, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw, obs_finset_sum hadd hsmul Finset.univ v
      (fun i : Fin (N + 1) => fun z : ℂ => z ^ (i : ℕ) * (Complex.Gamma z)⁻¹)
      (fun i => (differentiable_id.pow _).mul differentiable_invGamma)]
    exact hvsum
  refine ⟨P, Q, hQne, hP.symm, differentiallyAlgebraic_polynomial P, fun lam hlam => ?_⟩
  refine ⟨?_, hypertranscendental_polynomial_add_gammaPerturbation hlam hQne P⟩
  have hpert : gammaPerturbation lam Q = fun z => lam * (Q.eval z * (Complex.Gamma z)⁻¹) := by
    funext z; rw [gammaPerturbation]; ring
  have hpertdiff : Differentiable ℂ (gammaPerturbation lam Q) :=
    differentiable_gammaPerturbation lam Q
  have hsum := hadd (fun z => P.eval z) (gammaPerturbation lam Q) P.differentiable hpertdiff
  have hzero : L (gammaPerturbation lam Q) = 0 := by
    rw [hpert, hsmul lam (fun z => Q.eval z * (Complex.Gamma z)⁻¹)
      (Q.differentiable.mul differentiable_invGamma), hQobs, smul_zero]
  rw [hsum, hzero, add_zero]
  exact hP.symm

end

end GaloisForLFunctions.HTGeometry
