import GaloisForLFunctions.RHTower.MobiusCausalMultiplierDeriv

/-!
# The derivative residue of zeta at its pole

Writing `ζ(s) = A(s) + G(s)/(s-1)` with `A` entire and `G = 1/Γℝ` entire, `G(1) = 1`, the
derivative of `ζ` has the exact pole profile

```text
(s-1)² ζ'(s) → -1        (s → 1).
```

This is the derivative companion of `riemannZeta_residue_one`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The entire reciprocal completed factor `G = 1/Γℝ`. -/
def gammaRInv (s : ℂ) : ℂ := (Complex.Gammaℝ s)⁻¹

theorem differentiable_gammaRInv : Differentiable ℂ gammaRInv :=
  Complex.differentiable_Gammaℝ_inv

theorem gammaRInv_one : gammaRInv 1 = 1 := by
  rw [gammaRInv, Complex.Gammaℝ_one, inv_one]

theorem riemannZeta_eq_poleFree_add {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = zetaPoleFree s + gammaRInv s / (s - 1) := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [zetaPoleFree, gammaRInv]
  field_simp
  ring

/-- The derivative of zeta in Laurent form. -/
theorem hasDerivAt_riemannZeta_laurent {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt riemannZeta
      (deriv zetaPoleFree s +
        (deriv gammaRInv s * (s - 1) - gammaRInv s * 1) / (s - 1) ^ 2) s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hA : HasDerivAt zetaPoleFree (deriv zetaPoleFree s) s :=
    (differentiable_zetaPoleFree s).hasDerivAt
  have hG : HasDerivAt gammaRInv (deriv gammaRInv s) s :=
    (differentiable_gammaRInv s).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => z - 1) 1 s := by
    simpa using (hasDerivAt_id s).sub_const 1
  have hsum := hA.add (hG.div hd hsub)
  have hopen : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact riemannZeta_eq_poleFree_add hz

/-- **The derivative residue.**  `(s-1)² ζ'(s) → -1` as `s → 1`. -/
theorem tendsto_sub_one_sq_mul_deriv_riemannZeta :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv riemannZeta s) (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds (-1)) := by
  have hA : ContinuousAt (deriv zetaPoleFree) 1 :=
    ((differentiable_zetaPoleFree.differentiableOn.analyticOnNhd isOpen_univ) 1
      (Set.mem_univ 1)).deriv.continuousAt
  have hG : ContinuousAt (deriv gammaRInv) 1 :=
    ((differentiable_gammaRInv.differentiableOn.analyticOnNhd isOpen_univ) 1
      (Set.mem_univ 1)).deriv.continuousAt
  have hG0 : ContinuousAt gammaRInv 1 := differentiable_gammaRInv.continuous.continuousAt
  have hsub : Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds 0) := by
    simpa using (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
  have h1 : Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv zetaPoleFree s) (nhds (1 : ℂ)) (nhds 0) := by
    have := (hsub.pow 2).mul hA.tendsto
    simpa using this
  have h2 : Tendsto (fun s : ℂ => deriv gammaRInv s * (s - 1) - gammaRInv s * 1)
      (nhds (1 : ℂ)) (nhds (-1)) := by
    have ha := hG.tendsto.mul hsub
    have hb := hG0.tendsto
    rw [gammaRInv_one] at hb
    have hb1 : Tendsto (fun s : ℂ => gammaRInv s * 1) (nhds (1 : ℂ)) (nhds 1) := by
      simpa using hb
    have := ha.sub hb1
    simpa using this
  have hmain := h1.add h2
  rw [zero_add] at hmain
  refine Tendsto.congr' ?_ (hmain.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := by
    intro h
    exact hs (by rw [h]; exact Set.mem_singleton 1)
  have hsub0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [(hasDerivAt_riemannZeta_laurent hs1).deriv]
  field_simp

end

end RHTower
