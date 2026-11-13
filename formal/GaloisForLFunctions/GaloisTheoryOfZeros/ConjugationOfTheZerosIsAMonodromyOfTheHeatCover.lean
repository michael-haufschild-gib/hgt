import GaloisForLFunctions.GaloisTheoryOfZeros.TheTransportsOverForwardTimesFormAGroup
import GaloisForLFunctions.RHTower.DeBruijnNewmanStrictBound

/-!
# Conjugation of the zeros is a monodromy of the heat cover

In the place variable `z` (`ρ = 1/2 + iz`) the reflection `r : ρ ↦ 1 − ρ` is `z ↦ −z` and the
involution `cr : ρ ↦ 1 − ρ̄` is the conjugation `z ↦ z̄`. Over a real time `t` both act on the
fibre of the heat cover. This file places them relative to the forward monodromy group.

* The reflection commutes with every forward monodromy
  (`forwardMonodromy_commute_fibreNeg`, previous file).
* **Conjugation is a monodromy.** Let `γ` be a forward path from a real time `t` to a real time
  `t'` over which all zeros are real. Transport along `γ` followed by the reversed conjugate
  path carries every zero `z₀` of `H_t` to `z̄₀` (`transports_conj_loop`): the conjugate path
  transports `z̄₀` to the conjugate of the real end point, which is the end point itself.
  Two forward times off the branch times are joined by a forward path, and all zeros are real
  at the time `1/8`. Hence the conjugation `fibreConj t` of the fibre over a positive real
  time `t`, not a branch time, is an element of the forward monodromy group
  (`fibreConj_mem_forwardMonodromy`).
* **The Riemann hypothesis** says that this element is the identity at every positive real time
  off the branch times (`riemannHypothesis_iff_fibreConj_eq_one`).
-/

open Complex Set
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The conjugate path -/

/-- The conjugate path of times. -/
def pathConj (γ : ℝ → ℂ) (s : ℝ) : ℂ := starRingEnd ℂ (γ s)

/-- The branch times are stable under conjugation. -/
theorem mem_branchTimes_of_conj_mem {τ : ℂ} (h : starRingEnd ℂ τ ∈ branchTimes) :
    τ ∈ branchTimes := by
  obtain ⟨⟨τ', w⟩, ⟨h0, h1⟩, hτ'⟩ := h
  have hτ'' : τ' = starRingEnd ℂ τ := hτ'
  subst hτ''
  refine ⟨(τ, starRingEnd ℂ w), ⟨?_, ?_⟩, rfl⟩
  · have := complexHeat_conj (starRingEnd ℂ τ) w
    rw [show complexHeat (starRingEnd ℂ τ) w = 0 from h0, map_zero, Complex.conj_conj] at this
    exact this.symm
  · have := iteratedDeriv_complexHeat_conj (starRingEnd ℂ τ) 1 w
    simp only [iteratedDeriv_one] at this
    rw [show deriv (complexHeat (starRingEnd ℂ τ)) w = 0 from h1, map_zero,
      Complex.conj_conj] at this
    exact this

theorem IsForwardPath.conj {γ : ℝ → ℂ} (h : IsForwardPath γ) : IsForwardPath (pathConj γ) :=
  ⟨Complex.continuous_conj.comp_continuousOn h.continuousOn, fun s hs => by
    rw [pathConj, Complex.conj_re]
    exact h.re_pos s hs, fun s hs hmem => h.simple s hs (mem_branchTimes_of_conj_mem hmem)⟩

/-! ## Conjugation of a real fibre -/

theorem complexHeat_ofReal_conj (t : ℝ) (z : ℂ) :
    complexHeat (t : ℂ) (starRingEnd ℂ z) = starRingEnd ℂ (complexHeat (t : ℂ) z) := by
  rw [complexHeat_conj, Complex.conj_ofReal]

/-- The conjugation `z ↦ z̄` of the fibre over a real time: the involution `ρ ↦ 1 − ρ̄`. -/
def fibreConj (t : ℝ) : Equiv.Perm {z : ℂ // complexHeat (t : ℂ) z = 0} where
  toFun p := ⟨starRingEnd ℂ p.1, by rw [complexHeat_ofReal_conj, p.2, map_zero]⟩
  invFun p := ⟨starRingEnd ℂ p.1, by rw [complexHeat_ofReal_conj, p.2, map_zero]⟩
  left_inv p := Subtype.ext (Complex.conj_conj _)
  right_inv p := Subtype.ext (Complex.conj_conj _)

/-- **Conjugation of the zeros is the transport along a loop.** If `γ` is a forward path from
the real time `t` to a real time `t'` over which all zeros are real, then the loop `γ` followed
by the reversed conjugate path transports every zero `z₀` of `H_t` to `z̄₀`. -/
theorem transports_conj_loop {γ : ℝ → ℂ} {t t' : ℝ} (hγ : IsForwardPath γ) (h0 : γ 0 = t)
    (h1 : γ 1 = t') (hreal : ∀ z : ℂ, complexHeat (t' : ℂ) z = 0 → z.im = 0) {z₀ : ℂ}
    (hz₀ : complexHeat (t : ℂ) z₀ = 0) :
    Transports (pathJoin γ (pathRev (pathConj γ))) z₀ (starRingEnd ℂ z₀) := by
  obtain ⟨z₁, hT⟩ := hγ.exists_transports (by rw [h0]; exact hz₀)
  have hz₁ : starRingEnd ℂ z₁ = z₁ := by
    have := hT.zero_right
    rw [h1] at this
    exact Complex.conj_eq_iff_im.2 (hreal z₁ this)
  have h2 : Transports (pathRev (pathConj γ)) (starRingEnd ℂ z₁) (starRingEnd ℂ z₀) :=
    hT.conj.symm
  rw [hz₁] at h2
  exact hT.trans h2

/-! ## Conjugation in the forward monodromy group -/

/-- A real time `t ≥ 1/8` is not a branch time: all zeros of `H_t` are simple. -/
theorem ofReal_not_mem_branchTimes_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) :
    (t : ℂ) ∉ branchTimes := by
  rintro ⟨⟨τ, z⟩, ⟨hz, hd⟩, hτ⟩
  have hτ' : τ = (t : ℂ) := hτ
  subst hτ'
  have hfun : complexHeat (t : ℂ) = riemannHeat t := funext (complexHeat_ofReal t)
  rw [hfun] at hz hd
  exact (riemannHeat_zeros_real_simple_of_eighth_le ht hz).2 hd

/-- **Conjugation is a forward monodromy.** Over a positive real time `t`, not a branch time,
the conjugation `z ↦ z̄` of the zeros of `H_t` is the transport along a loop of forward times. -/
theorem fibreConj_mem_forwardMonodromy {t : ℝ} (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes) :
    fibreConj t ∈ forwardMonodromy (t : ℂ) (by rw [Complex.ofReal_re]; exact ht) hb := by
  obtain ⟨γ, hγ, h0, h1⟩ := exists_isForwardPath (τ := (t : ℂ)) (τ' := ((1 / 8 : ℝ) : ℂ))
    (by rw [Complex.ofReal_re]; exact ht) (by rw [Complex.ofReal_re]; norm_num) hb
    (ofReal_not_mem_branchTimes_of_eighth_le le_rfl)
  have hreal : ∀ z : ℂ, complexHeat ((1 / 8 : ℝ) : ℂ) z = 0 → z.im = 0 := fun z hz => by
    rw [complexHeat_ofReal] at hz
    exact (riemannHeat_zeros_real_simple_of_eighth_le le_rfl hz).1
  refine ⟨pathJoin γ (pathRev (pathConj γ)), hγ.join hγ.conj.reverse ?_, ?_, ?_,
    fun p => transports_conj_loop hγ h0 h1 hreal p.2⟩
  · rw [pathRev_zero, pathConj, h1, Complex.conj_ofReal]
  · rw [pathJoin_zero, h0]
  · rw [pathJoin_one, pathRev_one, pathConj, h0, Complex.conj_ofReal]

/-- **The Riemann hypothesis in the forward monodromy group.** RH holds iff the conjugation of
the fibre is the identity over every positive real time off the branch times. -/
theorem riemannHypothesis_iff_fibreConj_eq_one :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → (t : ℂ) ∉ branchTimes → fibreConj t = 1 := by
  constructor
  · intro hRH t ht _
    refine Equiv.ext fun p => Subtype.ext ?_
    have hz : riemannHeat t p.1 = 0 := by
      rw [← complexHeat_ofReal]
      exact p.2
    exact Complex.conj_eq_iff_im.2 (riemannHeat_zeros_real_simple_of_riemannHypothesis hRH ht hz).1
  · intro h
    rw [riemannHypothesis_iff_newmanConstant_eq_zero]
    refine le_antisymm ?_ newmanConstant_nonneg
    by_contra hcon
    rw [not_le] at hcon
    -- a time in `[Λ/4, Λ/2]` off the branch times
    obtain ⟨t, ht, htb⟩ : ∃ t ∈ Icc (newmanConstant / 4) (newmanConstant / 2),
        (t : ℂ) ∉ branchTimes := by
      by_contra hall
      push Not at hall
      have hfin := finite_branchTimes_box (t₀ := newmanConstant / 4) (newmanConstant / 2)
        (by linarith)
      have hsub : Complex.ofReal '' Icc (newmanConstant / 4) (newmanConstant / 2) ⊆
          {τ : ℂ | τ ∈ branchTimes ∧ newmanConstant / 4 ≤ τ.re ∧ ‖τ‖ ≤ newmanConstant / 2} := by
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨hall t ht, by rw [Complex.ofReal_re]; exact ht.1, ?_⟩
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
        exact ht.2
      exact (Icc_infinite (by linarith : newmanConstant / 4 < newmanConstant / 2)).image
        Complex.ofReal_injective.injOn (hfin.subset hsub)
    have ht0 : 0 < t := by linarith [ht.1]
    have hone := h t ht0 htb
    have hmem : t ∈ realRootedTimes := by
      refine ⟨ht0.le, fun z hz => ?_⟩
      have hz' : complexHeat (t : ℂ) z = 0 := by
        rw [complexHeat_ofReal]
        exact hz
      have := congrArg
        (fun σ : Equiv.Perm {z : ℂ // complexHeat (t : ℂ) z = 0} => (σ ⟨z, hz'⟩).1) hone
      exact Complex.conj_eq_iff_im.1 this
    have := (mem_realRootedTimes_iff ht0.le).1 hmem
    linarith [ht.2]

end

end GaloisForLFunctions.GaloisTheoryOfZeros
