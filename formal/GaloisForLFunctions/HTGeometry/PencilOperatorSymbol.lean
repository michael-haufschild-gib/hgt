import GaloisForLFunctions.HTGeometry.PencilOperatorKernelCore

/-!
# A constant operator carrier kills the whole symbol combination

Running the facet isolation of `PencilSRRealization` with an operator `𝒟 = ∑_r δ^r P_r(T)`: after
multiplying by one escaping variable per other facet the carrier collapses to a single phase
composite whose inner function is `∑_r (L_A w)^r · Θ^r (Ψ_{A, D·P_r})`.  Because `exp ∘ L_A` covers
the punctured plane, constancy of the carrier makes that inner function constant, so all its Taylor
coefficients of positive order vanish; since `Θ` is diagonal this is exactly

```text
∑_r (m · L_A w)^r · symb_A(m, P_r) = 0     for every m ≥ 1,
```

after dividing by the nonzero symbol of the isolating product.

* `inner_iteratedDeriv_eq_zero_of_const` — constancy of a phase composite kills the inner
  coefficients;
* `symbHom_combination_eq_zero` — the symbol identity.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ} {α : Type*} [DecidableEq α] {facets : Finset (Finset α)}

/-- A constant phase composite has vanishing inner Taylor coefficients of positive order. -/
theorem inner_iteratedDeriv_eq_zero_of_const {L : (Fin d → ℂ) →ₗ[ℂ] ℂ}
    (hL : Function.Surjective fun z : Fin d → ℂ => L z) {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hconst : ∀ z z' : Fin d → ℂ, phaseComp L Φ z = phaseComp L Φ z')
    {m : ℕ} (hm : 1 ≤ m) : iteratedDeriv m Φ 0 = 0 := by
  obtain ⟨z₀, hz₀⟩ := hL 0
  have hpunct : ∀ u : ℂ, u ≠ 0 → Φ u = Φ (Complex.exp (L z₀)) := by
    intro u hu
    obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, Complex.exp (L z) = u := by
      obtain ⟨z, hz⟩ := hL (Complex.log u)
      have hz' : L z = Complex.log u := hz
      exact ⟨z, by rw [hz', Complex.exp_log hu]⟩
    rw [← hz]
    exact hconst z z₀
  have hall : ∀ u, Φ u = Φ (Complex.exp (L z₀)) := eq_of_eq_on_punctured hΦ hpunct
  have hfun : Φ = fun _ => Φ (Complex.exp (L z₀)) := funext hall
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [hfun, iteratedDeriv_succ']
  simp

/-- **The symbol identity of a constant operator carrier.** -/
theorem symbHom_combination_eq_zero (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z)
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (w : Fin d → ℂ)
    {A : Finset α} (hA : A ∈ facets) {n : ℕ} (P : Fin n → MvPolynomial α ℂ)
    (hconst : ∀ z z' : Fin d → ℂ,
      (∑ r : Fin n, (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r))) z
        = (∑ r : Fin n, (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r))) z')
    {m : ℕ} (hm : 1 ≤ m) :
    ∑ r : Fin n, ((m : ℂ) * Lin A w) ^ (r : ℕ)
        * symbHom S.ω (S.phase A) (m : ℂ) (P r) = 0 := by
  classical
  -- one escaping vertex per other facet
  have hex : ∀ B : {x // x ∈ facets.erase A}, ∃ v, v ∈ A ∧ v ∉ (B : Finset α) := by
    intro B
    obtain ⟨hBA, hBmem⟩ := Finset.mem_erase.mp B.2
    by_contra hcon
    have hsub : A ⊆ (B : Finset α) := by
      intro x hx
      by_contra hxB
      exact hcon ⟨x, hx, hxB⟩
    exact hBA (hanti (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hBmem) hsub).symm
  choose sel hselA hselB using hex
  set D : MvPolynomial α ℂ := ∏ B : {x // x ∈ facets.erase A}, X (sel B) with hD
  -- the shifted operator carrier is still constant, and isolates the facet
  set Ψ : Fin n → ℂ → ℂ :=
    fun r => dilateSumHom (polyShift S.ω (D * P r)) (S.phase A) with hΨ
  set Φ : ℂ → ℂ := fun u => ∑ r : Fin n, (Lin A w) ^ (r : ℕ) * (eulerOp^[(r : ℕ)] (Ψ r)) u with hΦ
  have hΨsmooth : ∀ r : Fin n, ContDiff ℂ (⊤ : ℕ∞) (Ψ r) := fun r => contDiff_dilateSumHom _ _
  have hΦdiff : Differentiable ℂ Φ := by
    rw [hΦ]
    refine Differentiable.fun_sum fun r _ => ?_
    exact ((contDiff_eulerOp_iterate (hΨsmooth r) (r : ℕ)).differentiable (by simp)).const_mul _
  have hisolate : ∀ r : Fin n,
      seedCarrierPoly S.ω S.seed (D * P r) = phaseComp (Lin A) (Ψ r) := by
    intro r
    funext z
    rw [S.seedCarrierPoly_isolate hA sel hselB (P r) z, seedCarrierPoly_expSeedHom]
    show dilateSumHom (polyShift S.ω (D * P r)) (S.phase A) (Complex.exp (S.phase A z))
      = dilateSumHom (polyShift S.ω (D * P r)) (S.phase A) (Complex.exp (Lin A z))
    rw [hLin A hA z]
  have hstep : ∀ r : Fin n,
      (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (D * P r))
        = phaseComp (Lin A) (fun u => (Lin A w) ^ (r : ℕ) * (eulerOp^[(r : ℕ)] (Ψ r)) u) := by
    intro r
    rw [hisolate r]
    exact dirDeriv_iterate_phaseComp (hΨsmooth r) w (r : ℕ)
  -- transport constancy through the isolating shift
  have hGconst : ∀ z z' : Fin d → ℂ, phaseComp (Lin A) Φ z = phaseComp (Lin A) Φ z' := by
    have hdiffiter : ∀ r : Fin n, ∀ j : ℕ,
        Differentiable ℂ ((dirDeriv w)^[j] (seedCarrierPoly S.ω S.seed (P r))) :=
      fun r j => differentiable_dirDeriv_iterate_seedCarrierPoly S Lin hLin (P r) w j
    have hsum : ∀ z : Fin d → ℂ, phaseComp (Lin A) Φ z
        = shiftAlgHom (polyShift S.ω D)
            (fun y => ∑ r : Fin n,
              (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r)) y) z := by
      intro z
      have hcomm : ∀ r : Fin n,
          shiftAlgHom (polyShift S.ω D)
              ((dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r)))
            = (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (D * P r)) := by
        intro r
        rw [seedCarrierPoly_mul, dirDeriv_iterate_shiftAlgHom _ w (hdiffiter r) (r : ℕ)]
      have hlin : shiftAlgHom (polyShift S.ω D)
            (fun y => ∑ r : Fin n,
              (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r)) y)
          = fun y => ∑ r : Fin n,
              shiftAlgHom (polyShift S.ω D)
                ((dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r))) y := by
        have hpi : (fun y => ∑ r : Fin n,
            (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r)) y)
            = ∑ r : Fin n, (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r)) := by
          funext y
          rw [Finset.sum_apply]
        rw [hpi, map_sum]
        funext y
        rw [Finset.sum_apply]
      rw [hlin]
      show ∑ r : Fin n, (Lin A w) ^ (r : ℕ) * (eulerOp^[(r : ℕ)] (Ψ r)) (Complex.exp (Lin A z))
        = ∑ r : Fin n, shiftAlgHom (polyShift S.ω D)
            ((dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r))) z
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hcomm r, hstep r]
      rfl
    intro z z'
    rw [hsum z, hsum z']
    have hCfun : (fun y => ∑ r : Fin n,
        (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r)) y)
        = fun _ => (∑ r : Fin n,
          (dirDeriv w)^[(r : ℕ)] (seedCarrierPoly S.ω S.seed (P r))) 0 := by
      funext y
      rw [← Finset.sum_apply]
      exact hconst y 0
    rw [hCfun, shiftAlgHom_const]
  -- the inner function is constant, so its positive coefficients vanish
  have hsurj : Function.Surjective fun z : Fin d → ℂ => Lin A z := by
    intro c
    obtain ⟨z, hz⟩ := S.phase_surjective A hA c
    have hz' : Lin A z = c := by rw [← hLin A hA z]; exact hz
    exact ⟨z, hz'⟩
  have hzero : iteratedDeriv m Φ 0 = 0 :=
    inner_iteratedDeriv_eq_zero_of_const hsurj hΦdiff hGconst hm
  -- read off the symbol identity
  have hcoeff : iteratedDeriv m Φ 0
      = ∑ r : Fin n, ((m : ℂ) * Lin A w) ^ (r : ℕ)
          * symbHom S.ω (S.phase A) (m : ℂ) (D * P r) := by
    rw [hΦ, iteratedDeriv_finset_sum _ m (fun r _ =>
      contDiff_const.mul ((contDiff_eulerOp_iterate (hΨsmooth r) (r : ℕ)).of_le (by exact_mod_cast le_top)))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [iteratedDeriv_const_mul' (contDiff_eulerOp_iterate (hΨsmooth r) (r : ℕ)) _ m]
    show (Lin A w) ^ (r : ℕ) * iteratedDeriv m (eulerOp^[(r : ℕ)] (Ψ r)) 0 = _
    rw [iteratedDeriv_eulerOp_iterate_zero (hΨsmooth r) (r : ℕ) m, hΨ]
    show (Lin A w) ^ (r : ℕ)
        * ((m : ℂ) ^ (r : ℕ)
          * iteratedDeriv m (dilateSumHom (polyShift S.ω (D * P r)) (S.phase A)) 0) = _
    rw [iteratedDeriv_dilateSumHom_zero, evAlgHom_polyShift]
    ring
  rw [hcoeff] at hzero
  -- divide out the symbol of the isolating product
  have hDsymb : symbHom S.ω (S.phase A) (m : ℂ) D ≠ 0 := by
    rw [hD, symbHom, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun B _ => ?_
    rw [aeval_X]
    intro hzz
    refine S.ratio_pow_ne_one hA (hselA B) hm ?_
    rw [S.ratio_pow]
    exact sub_eq_zero.mp hzz
  have hfactor : ∑ r : Fin n, ((m : ℂ) * Lin A w) ^ (r : ℕ)
      * symbHom S.ω (S.phase A) (m : ℂ) (D * P r)
      = symbHom S.ω (S.phase A) (m : ℂ) D
        * ∑ r : Fin n, ((m : ℂ) * Lin A w) ^ (r : ℕ)
          * symbHom S.ω (S.phase A) (m : ℂ) (P r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [symbHom_mul]
    ring
  rw [hfactor] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hDsymb

end

end GaloisForLFunctions.HTGeometry
