import GaloisForLFunctions.RHTower.XiFirstOrderLaguerrePolyaMaximality

/-!
# No real-rooted polynomial operator maps the Laguerre–Pólya class onto `Ξ`

Let `φ(z) = z^m ∏_i (1 − c_i z)` with real `c_i`, at least one `c_i ≠ 0`.  Then no Laguerre–Pólya
`f` has `φ(D)f = Ξ` (`not_exists_laguerrePolya_firstOrderChain_iterate_deriv_preimage_XiC`).  Up
to a real scalar, this covers every real-rooted real polynomial `φ` with a nonzero root: any
degree, zeros of any signs, and any order of vanishing at `0`.

The Laguerre–Pólya class is closed under `1 − cD` (`laguerrePolya_sub_smul_deriv`) and under `D`
(`laguerrePolya_deriv`: by Rolle the derivative of a real-rooted polynomial is real-rooted,
`splits_derivative`).  Peeling factors from the outside, the first factor with `c ≠ 0` exhibits
a first-order Laguerre–Pólya preimage of `Ξ`, which does not exist
(`KernelStrip.not_exists_laguerrePolya_firstOrder_preimage_XiC`).
-/

open Polynomial Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- **Rolle.**  The derivative of a real-rooted real polynomial is real-rooted. -/
theorem splits_derivative {p : ℝ[X]} (hp : p.Splits) : (derivative p).Splits := by
  rw [splits_iff_card_roots] at hp ⊢
  refine le_antisymm (card_roots' _) ?_
  have h1 := Polynomial.card_roots_le_derivative p
  have h2 := Polynomial.natDegree_derivative_le p
  omega

/-- **The Laguerre–Pólya class is closed under `D`.** -/
theorem laguerrePolya_deriv {F : ℂ → ℂ} (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (deriv F) := by
  obtain ⟨p, hsplit, hconv⟩ := hF
  refine ⟨fun m => derivative (p m), fun m => splits_derivative (hsplit m), ?_⟩
  have hd := tendstoLocallyUniformly_iterate_deriv hconv (fun m => differentiable_polyEvalC (p m)) 1
  simp only [Function.iterate_one] at hd
  have hfun : (fun m => polyEvalC (derivative (p m))) = fun m => deriv (polyEvalC (p m)) := by
    funext m
    rw [deriv_polyEvalC]
  rw [hfun]
  exact hd

theorem laguerrePolya_iterate_deriv {F : ℂ → ℂ}
    (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) (m : ℕ) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (deriv^[m] F) := by
  induction m with
  | zero => simpa using hF
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact laguerrePolya_deriv ih

/-- **Zero factors allowed.**  If `l` contains a nonzero `c`, no Laguerre–Pólya `f` satisfies
`∏_{c ∈ l}(1 − cD) f = Ξ`; entries `c = 0` act as the identity. -/
theorem not_exists_laguerrePolya_firstOrderChain_preimage_XiC_of_exists_ne {l : List ℝ}
    (hl : ∃ c ∈ l, c ≠ 0) :
    ¬ ∃ f : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya f ∧
      KernelStrip.firstOrderChain l f = XiC := by
  rintro ⟨f, hf, heq⟩
  induction l with
  | nil => obtain ⟨c, hc, -⟩ := hl; simp at hc
  | cons c l ih =>
    by_cases hc : c = 0
    · apply ih
      · obtain ⟨c', hc', hne⟩ := hl
        rcases List.mem_cons.mp hc' with rfl | h
        · exact absurd hc hne
        · exact ⟨c', h, hne⟩
      · rw [← heq]
        funext z
        simp [KernelStrip.firstOrderChain, hc]
    · refine KernelStrip.not_exists_laguerrePolya_firstOrder_preimage_XiC (a := 1 / c)
        (one_div_ne_zero hc) ⟨KernelStrip.firstOrderChain l f,
          KernelStrip.laguerrePolya_firstOrderChain l hf, fun z => ?_⟩
      rw [one_div_one_div, ← heq]
      rfl

/-- **With derivative factors.**  If `l` contains a nonzero `c`, then for every `m` no
Laguerre–Pólya `f` satisfies `D^m ∏_{c ∈ l}(1 − cD) f = Ξ`, written as
`∏_{c ∈ l}(1 − cD)(D^m f) = Ξ`. -/
theorem not_exists_laguerrePolya_firstOrderChain_iterate_deriv_preimage_XiC {l : List ℝ}
    (hl : ∃ c ∈ l, c ≠ 0) (m : ℕ) :
    ¬ ∃ f : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya f ∧
      KernelStrip.firstOrderChain l (deriv^[m] f) = XiC := by
  rintro ⟨f, hf, heq⟩
  exact not_exists_laguerrePolya_firstOrderChain_preimage_XiC_of_exists_ne hl
    ⟨deriv^[m] f, laguerrePolya_iterate_deriv hf m, heq⟩

end

end RHTower
