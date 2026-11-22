import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.Statement

/-! Zeros in the positive half-plane retain their multiplicities after a level change. -/

open Complex Filter Topology

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

theorem lFunction_analyticAt {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) : AnalyticAt ℂ χ.LFunction s := by
  rcases hs with hχ | hs
  · exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  · let U : Set ℂ := {1}ᶜ
    have hopen : IsOpen U := isClosed_singleton.isOpen_compl
    exact (show DifferentiableOn ℂ χ.LFunction U from fun z hz =>
      (χ.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt).analyticAt (hopen.mem_nhds hs)

theorem re_lt_one_of_isLZero {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M}
    {s : ℂ} (h : IsLZero χ s) : s.re < 1 :=
  lt_of_not_ge fun hre => χ.LFunction_ne_zero_of_one_le_re h.1 hre h.2

/-- The order and zero predicate on `Re s > 0` are unchanged by the finite Euler product. -/
theorem zero_changeLevel {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M)
    (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) (hreg : ψ ≠ 1 ∨ s ≠ 1) :
    (IsLZero (ψ.changeLevel hNM) s ↔ IsLZero ψ s) ∧
      analyticOrderNatAt (ψ.changeLevel hNM).LFunction s = analyticOrderNatAt ψ.LFunction s := by
  let E (z : ℂ) := ∏ p ∈ M.primeFactors, (1 - ψ p * (p : ℂ) ^ (-z))
  have hdiff : Differentiable ℂ E := by
    intro z
    have h := DifferentiableAt.finsetProd (𝕜 := ℂ) (x := z) (u := M.primeFactors)
      (f := fun p w => 1 - ψ p * (p : ℂ) ^ (-w)) (fun p hp => by
        have hp₀ : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
          ((differentiableAt_id.neg).const_cpow (Or.inl hp₀))))
    rwa [Finset.prod_fn] at h
  have he : E s ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
    have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp₁ (neg_neg_of_pos hs)
    have h := (mul_le_of_le_one_left (norm_nonneg ((p : ℂ) ^ (-s)))
      (ψ.norm_le_one (p : ZMod N))).trans_lt hnorm
    intro hzero
    rw [← norm_mul, ← sub_eq_zero.mp hzero, norm_one] at h
    exact (lt_irrefl (1 : ℝ)) h
  have hreg' : ∀ᶠ z : ℂ in 𝓝 s, ψ ≠ 1 ∨ z ≠ 1 := by
    rcases hreg with hp | hs'
    · exact Eventually.of_forall fun _ => Or.inl hp
    · filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hs'] with z hz
      exact Or.inr hz
  have hregM : ψ.changeLevel hNM ≠ 1 ∨ s ≠ 1 :=
    hreg.imp_left fun h h₁ => h ((DirichletCharacter.changeLevel_eq_one_iff hNM).mp h₁)
  have hfun : (ψ.changeLevel hNM).LFunction =ᶠ[𝓝 s] ψ.LFunction * E := by
    filter_upwards [hreg'] with z hz
    exact DirichletCharacter.LFunction_changeLevel hNM ψ hz
  refine ⟨?_, ?_⟩
  · change ((ψ.changeLevel hNM ≠ 1 ∨ s ≠ 1) ∧ (ψ.changeLevel hNM).LFunction s = 0 ↔
      (ψ ≠ 1 ∨ s ≠ 1) ∧ ψ.LFunction s = 0)
    rw [DirichletCharacter.LFunction_changeLevel hNM ψ hreg, mul_eq_zero, or_iff_left he]
    exact ⟨fun h => ⟨hreg, h.2⟩, fun h => ⟨hregM, h.2⟩⟩
  · unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hfun, analyticOrderAt_mul (lFunction_analyticAt ψ hreg) (hdiff.analyticAt s),
      (hdiff.analyticAt s).analyticOrderAt_eq_zero.mpr he, add_zero]

end QH.PrimeProgressions
