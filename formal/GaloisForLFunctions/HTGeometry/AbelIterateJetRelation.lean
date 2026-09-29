import GaloisForLFunctions.HTGeometry.AbelIterateCoherence
import GaloisForLFunctions.HTGeometry.LinearizedTowerCoherence
import GaloisForLFunctions.HTGeometry.ParabolicFatouJetRealization
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# A differentially algebraic Abel function forces one equation on all iterates

Let `g` be an analytic self-map of an open connected set `D` and `A` a nonconstant analytic Abel
function, `A ∘ g = A + 1` on `D`.  If `A` satisfies an algebraic differential equation on `D`, then
a single nonzero polynomial `Q` with constant coefficients satisfies

`Q(gⁿ, (gⁿ)′, …, (gⁿ)^{(r)}) = 0` on `D` for **every** `n`.

This is the coherence theorem of Boshernitzan–Rubel for the iterates of `g`.  In the field of
meromorphic functions on `D`, `v = A'` and its substitutions `A^{(j)} ∘ gⁿ` obey
`A'(gⁿ)·(gⁿ)′ = A'` and the chain rule, and `A'` has finite transcendence degree; the abstract
Abel tower theorem (`AbelIterateCoherence`) gives the uniform relation.
-/

open Filter Topology Set Bottcher

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A substitution with a noncritical point is faithful.**  Near a point where `g′ ≠ 0` the map
`g` has an analytic local inverse, so a function vanishing along `g` vanishes on an open set. -/
theorem substitutionFaithful_of_deriv_ne_zero {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hVc : IsPreconnected V) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hmaps : MapsTo g U V)
    {t₀ : ℂ} (ht₀ : t₀ ∈ U) (hd : deriv g t₀ ≠ 0) : SubstitutionFaithful U V g := by
  obtain ⟨ρ, hρan, hρg, hgρ⟩ := exists_localInverse_analytic (hg t₀ ht₀) hd
  have hρ0 : ρ (g t₀) = t₀ := hρg.self_of_nhds
  have hρU : ∀ᶠ w in 𝓝 (g t₀), ρ w ∈ U :=
    hρan.continuousAt.preimage_mem_nhds (by rw [hρ0]; exact hUo.mem_nhds ht₀)
  have hV : ∀ᶠ w in 𝓝 (g t₀), w ∈ V := hVo.mem_nhds (hmaps ht₀)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hρU.and (hV.and hgρ))
  exact substitutionFaithful_of_rightInverse (ρ := ρ) (W := Metric.ball (g t₀) ε) hVc
    Metric.isOpen_ball (Metric.nonempty_ball.mpr hε) (fun w hw => (hball w hw).2.1)
    (fun w hw => (hball w hw).1) (fun w hw => (hball w hw).2.2)

/-- The scalar embedding of a meromorphic function field is the constant element. -/
theorem algebraMap_complex_eq_constMeroElement {W : Set ℂ} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWne : W.Nonempty) (hWinf : W.Infinite) (c : ℂ) :
    letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
    letI : Algebra ℂ (meroField W) :=
      ((ratfuncToMero W hWo hWc hWne hWinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
    algebraMap ℂ (meroField W) c
      = analyticMeroElement (fun _ : ℂ => c) (analyticOnNhd_const (v := c)) := by
  letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
  show ratfuncToMero W hWo hWc hWne hWinf (algebraMap ℂ (RatFunc ℂ) c) = _
  rw [algebraMap_complex_meroField hWo hWc hWne hWinf c]
  rfl

variable {D : Set ℂ} {g A : ℂ → ℂ}

theorem analyticOnNhd_iterate (hg : AnalyticOnNhd ℂ g D) (hmaps : MapsTo g D D) (n : ℕ) :
    AnalyticOnNhd ℂ (g^[n]) D := by
  induction n with
  | zero => exact analyticOnNhd_id
  | succ n ih =>
      rw [Function.iterate_succ]
      exact ih.comp hg hmaps

theorem abel_iterate (hmaps : MapsTo g D D) (habel : ∀ t ∈ D, A (g t) = A t + 1) (n : ℕ) :
    ∀ t ∈ D, A (g^[n] t) = A t + n := by
  induction n with
  | zero => intro t _; simp
  | succ n ih =>
      intro t ht
      rw [Function.iterate_succ_apply', habel _ (hmaps.iterate n ht), ih t ht]
      push_cast
      ring

/-- Differentiating the iterated Abel equation: `A'(gⁿ)·(gⁿ)′ = A'`. -/
theorem deriv_abel_iterate (hDo : IsOpen D) (hg : AnalyticOnNhd ℂ g D) (hmaps : MapsTo g D D)
    (hA : AnalyticOnNhd ℂ A D) (habel : ∀ t ∈ D, A (g t) = A t + 1) (n : ℕ) :
    ∀ t ∈ D, deriv A (g^[n] t) * deriv (g^[n]) t = deriv A t := by
  intro t ht
  have hev : (fun s => A (g^[n] s)) =ᶠ[𝓝 t] fun s => A s + n := by
    filter_upwards [hDo.mem_nhds ht] with s hs using abel_iterate hmaps habel n s hs
  have h1 := Filter.EventuallyEq.deriv_eq hev
  rw [show (fun s => A (g^[n] s)) = A ∘ g^[n] from rfl,
    deriv_comp t (hA _ (hmaps.iterate n ht)).differentiableAt
      (analyticOnNhd_iterate hg hmaps n t ht).differentiableAt,
    deriv_add_const] at h1
  exact h1

/-- **Boshernitzan–Rubel coherence for an Abel equation.**  If a nonconstant analytic `A` with
`A ∘ g = A + 1` on `D` satisfies an algebraic differential equation on `D`, then one nonzero
polynomial with constant coefficients annihilates the jets of every iterate `gⁿ` on `D`. -/
theorem exists_uniform_jet_relation_of_abel (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hg : AnalyticOnNhd ℂ g D) (hmaps : MapsTo g D D) (hA : AnalyticOnNhd ℂ A D)
    (habel : ∀ t ∈ D, A (g t) = A t + 1) {t₀ : ℂ} (ht₀ : t₀ ∈ D) (hA' : deriv A t₀ ≠ 0)
    (hDA : DifferentiallyAlgebraicOn A D) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ), Q ≠ 0 ∧
      ∀ n : ℕ, ∀ z ∈ D, MvPolynomial.eval
        (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (g^[n]) z) Q = 0 := by
  classical
  have hDne : D.Nonempty := ⟨t₀, ht₀⟩
  have hDinf : D.Infinite := infinite_of_mem_nhds t₀ (hDo.mem_nhds ht₀)
  letI := Bottcher.isDomain_analyticSubring D hDo hDc hDne
  letI : Algebra ℤ (meroField D) := Ring.toIntAlgebra _
  letI : Algebra ℂ (meroField D) :=
    ((ratfuncToMero D hDo hDc hDne hDinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
  letI := meroFieldDifferential hDo hDc hDne
  -- the iterates
  have hgn : ∀ n, AnalyticOnNhd ℂ (g^[n]) D := analyticOnNhd_iterate hg hmaps
  have hmapsn : ∀ n, MapsTo (g^[n]) D D := fun n => hmaps.iterate n
  have hchainD := deriv_abel_iterate hDo hg hmaps hA habel
  have hgn' : ∀ n, deriv (g^[n]) t₀ ≠ 0 := by
    intro n h
    have := hchainD n t₀ ht₀
    rw [h, mul_zero] at this
    exact hA' this.symm
  have hfaith : ∀ n, SubstitutionFaithful D D (g^[n]) := fun n =>
    substitutionFaithful_of_deriv_ne_zero hDo hDo hDc (hgn n) (hmapsn n) ht₀ (hgn' n)
  -- the substitution homomorphisms
  have hcomm : ∀ (n : ℕ) (x : ℂ),
      substMero hDo hDc hDne hDo hDc hDne (hgn n) (hmapsn n) (hfaith n)
        (algebraMap ℂ (meroField D) x) = algebraMap ℂ (meroField D) x := by
    intro n x
    rw [algebraMap_complex_eq_constMeroElement hDo hDc hDne hDinf x,
      substMero_analyticMeroElement]
    rfl
  set σ : ℕ → (meroField D →ₐ[ℂ] meroField D) := fun n =>
    { substMero hDo hDc hDne hDo hDc hDne (hgn n) (hmapsn n) (hfaith n) with
      commutes' := hcomm n } with hσdef
  have hσinj : ∀ n, Function.Injective (σ n) := fun n => (σ n).toRingHom.injective
  have hσelt : ∀ (n : ℕ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f D),
      σ n (analyticMeroElement f hf)
        = analyticMeroElement (f ∘ g^[n]) (hf.comp (hgn n) (hmapsn n)) := fun n f hf =>
    substMero_analyticMeroElement hDo hDc hDne hDo hDc hDne (hgn n) (hmapsn n) (hfaith n) f hf
  -- the jets of `A'` and the iterates as meromorphic functions
  set δ : Derivation ℤ (meroField D) (meroField D) :=
    Differential.deriv (R := meroField D) with hδ
  set v : ℕ → meroField D := fun j =>
    analyticMeroElement (iteratedDeriv (j + 1) A) (analyticOnNhd_iteratedDeriv hA (j + 1))
    with hvdef
  set y : ℕ → meroField D := fun n => analyticMeroElement (g^[n]) (hgn n) with hydef
  have hv : ∀ j, δ (v j) = v (j + 1) := by
    intro j
    rw [hvdef, hδ, deriv_analyticMeroElement_open hDo hDc hDne]
    refine analyticMeroElement_congr_eqOn _ _ fun t _ => ?_
    rw [← iteratedDeriv_succ]
  have hdy : ∀ n, δ (y n) = analyticMeroElement (deriv (g^[n])) (hgn n).deriv := fun n => by
    rw [hydef, hδ, deriv_analyticMeroElement_open hDo hDc hDne]
  have hv0 : v 0 ≠ 0 := by
    rw [hvdef, Ne, analyticMeroElement_eq_zero_iff]
    intro h
    exact hA' (by simpa [iteratedDeriv_one] using h t₀ ht₀)
  have hy : ∀ n, δ (y n) = v 0 * (σ n (v 0))⁻¹ := by
    intro n
    have hσv : σ n (v 0) ≠ 0 := fun h => hv0 (hσinj n (by rw [h, map_zero]))
    rw [eq_mul_inv_iff_mul_eq₀ hσv, hdy, hvdef, hσelt, ← analyticMeroElement_mul]
    refine analyticMeroElement_congr_eqOn _ _ fun t ht => ?_
    simp only [Function.comp_apply, zero_add, iteratedDeriv_one]
    rw [mul_comm]
    exact hchainD n t ht
  have hchain : ∀ n j, δ (σ n (v j)) = σ n (v (j + 1)) * δ (y n) := by
    intro n j
    rw [hdy, hvdef, hσelt, hσelt, hδ, deriv_analyticMeroElement_open hDo hDc hDne,
      ← analyticMeroElement_mul]
    refine analyticMeroElement_congr_eqOn _ _ fun t ht => ?_
    exact deriv_iteratedDeriv_comp hA (hgn n) (hmapsn n) (j + 1) ht
  -- the constants are killed by the derivation
  have hKconst : ∀ x : ℂ, δ (algebraMap ℂ (meroField D) x) = 0 := by
    intro x
    rw [algebraMap_complex_eq_constMeroElement hDo hDc hDne hDinf x, hδ,
      deriv_analyticMeroElement_open hDo hDc hDne]
    rw [analyticMeroElement_eq_zero_iff]
    intro t _
    simp
  -- the witness family for the jets of `A`
  obtain ⟨p, b, hb⟩ := exists_jet_algebraicWitness_family hDo hDc hDne hDinf hA hDA
  obtain ⟨Q, hQ0, hQ⟩ := exists_uniform_jet_relation_of_abel_tower δ hKconst σ hσinj v hv y hy
    hchain b fun j => hb (j + 1)
  refine ⟨p + p + 1, Q, hQ0, fun n z hz => ?_⟩
  have hjet : ∀ k : ℕ, (⇑δ)^[k] (y n)
      = analyticMeroElement (iteratedDeriv k (g^[n])) (analyticOnNhd_iteratedDeriv (hgn n) k) :=
    fun k => differentialJet_analyticMeroElement hDo hDc hDne _ (hgn n) k
  have hfin := hQ n
  rw [show (fun k : Fin (p + p + 1 + 1) => (⇑δ)^[(k : ℕ)] (y n))
      = fun k : Fin (p + p + 1 + 1) => analyticMeroElement (iteratedDeriv (k : ℕ) (g^[n]))
        (analyticOnNhd_iteratedDeriv (hgn n) (k : ℕ)) from funext fun k => hjet k] at hfin
  exact (aeval_analyticMeroElement_eq_zero_iff hDo hDc hDne hDinf
    (fun k : Fin (p + p + 1 + 1) => iteratedDeriv (k : ℕ) (g^[n]))
    (fun k => analyticOnNhd_iteratedDeriv (hgn n) (k : ℕ)) Q).mp hfin z hz

end

end GaloisForLFunctions.HTGeometry
