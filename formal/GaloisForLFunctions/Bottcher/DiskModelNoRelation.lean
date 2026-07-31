/-
# No polynomial relation for the disk model — transcendence of `h` over `ℂ(t)`

The capstone of the disk side: for `c ∉ {0, -2}`, an even FE-solution `h` on the unit disk with
`h 0 = 1` satisfies **no** nonzero polynomial relation `P(t, h t) = 0` (`P ∈ ℂ[t][Y]`,
`natDegree ≥ 1`). Mirrors the proven U0 architecture (`u0_no_relation`): strong induction on the
`Y`-degree; an irreducible (hence separable, char 0) relation has a *finite* circle bad set — the
zero locus of `leadingCoeff · (∂P).leadingCoeff · resultant(P, ∂P)` — so a whole boundary arc avoids
it (`exists_arc_avoiding_finite`); at every arc point the fibre is separable
(`separable_specialize`) and branch exhaustion continues `h` across
(`continuesAcross_of_separable_fibre_disk`), contradicting the proven natural boundary
(`natural_boundary_of_even_fe`). A reducible relation splits by integer normalization and the
integral-domain property of analytic functions on the ball (`analytic_domain_ball`).
-/
import GaloisForLFunctions.Bottcher.DiskModelContinuation
import GaloisForLFunctions.Bottcher.DiskAlgebraicContinuation
import GaloisForLFunctions.Bottcher.BoundaryArcCovering
open Polynomial Filter Topology Metric Complex Set HolomorphicIFT
open scoped nonZeroDivisors
namespace Bottcher
noncomputable section

/-- The ring of analytic functions on the unit ball is an integral domain (identity theorem). -/
theorem analytic_domain_ball {g h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hh : AnalyticOnNhd ℂ h (ball 0 1))
    (hgh : ∀ z ∈ ball (0:ℂ) 1, g z * h z = 0) :
    (∀ z ∈ ball (0:ℂ) 1, g z = 0) ∨ (∀ z ∈ ball (0:ℂ) 1, h z = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨z₁, hz₁E, hgz₁⟩, ⟨z₂, hz₂E, hhz₂⟩⟩ := hcon
  have hgne : ∀ᶠ z in 𝓝 z₁, g z ≠ 0 := (hg z₁ hz₁E).continuousAt.eventually_ne hgz₁
  have hExt_nhds : ball (0:ℂ) 1 ∈ 𝓝 z₁ := isOpen_ball.mem_nhds hz₁E
  have hzero_near : ∀ᶠ z in 𝓝 z₁, h z = 0 := by
    filter_upwards [hgne, hExt_nhds] with z hgz hzE
    rcases mul_eq_zero.mp (hgh z hzE) with h1 | h2
    · exact absurd h1 hgz
    · exact h2
  have hfreq : ∃ᶠ z in 𝓝[≠] z₁, h z = 0 :=
    (hzero_near.filter_mono nhdsWithin_le_nhds).frequently
  have hEqOn := hh.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0:ℂ) 1).isPreconnected hz₁E hfreq
  exact hhz₂ (hEqOn hz₂E)

/-- `t ↦ P(t, h t)` is analytic on the ball when `h` is. -/
theorem relation_analytic_ball {h : ℂ → ℂ} (hhd : DifferentiableOn ℂ h (ball 0 1))
    (P : (Polynomial ℂ)[X]) :
    AnalyticOnNhd ℂ (fun z => P.eval₂ (evalRingHom z) (h z)) (ball 0 1) := by
  have hha : AnalyticOnNhd ℂ h (ball 0 1) := hhd.analyticOnNhd isOpen_ball
  intro z hz
  have h2 : AnalyticAt ℂ (fun w : ℂ => (w, h w)) z :=
    analyticAt_id.prod (hha z hz)
  exact (bivar_analytic P (z, h z)).comp_of_eq h2 rfl

/-- **No separable relation for the disk model.** The finite bad set misses a whole boundary arc;
per-point branch-exhaustion continuation there contradicts the natural boundary. -/
theorem h_separable_no_relation {h : ℂ → ℂ} {c : ℂ}
    (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ z ∈ ball (0:ℂ) 1, h (-z) = h z)
    (hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2)
    (hh0 : h 0 = 1)
    (P : (Polynomial ℂ)[X])
    (hsep : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable)
    (hdeg : 1 ≤ P.natDegree)
    (hrel : ∀ t ∈ ball (0:ℂ) 1, P.eval₂ (evalRingHom t) (h t) = 0) : False := by
  have hP_ne : P ≠ 0 := fun h' => by rw [h', natDegree_zero] at hdeg; omega
  have hderiv_ne : derivative P ≠ 0 := by
    intro h'
    have := derivative_eq_zero.mp h'
    omega
  have hlc1 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP_ne
  have hlc2 : (derivative P).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hderiv_ne
  have hres : resultant P (derivative P) ≠ 0 := resultant_ne_zero_of_separable P hsep
  set q : ℂ[X] := P.leadingCoeff * (derivative P).leadingCoeff * resultant P (derivative P)
    with hq
  have hq_ne : q ≠ 0 := by rw [hq]; exact mul_ne_zero (mul_ne_zero hlc1 hlc2) hres
  have hFfin : {x : ℂ | q.IsRoot x}.Finite := finite_setOf_isRoot hq_ne
  obtain ⟨ζ₀, r, hζ₀norm, hrpos, harc⟩ := exists_arc_avoiding_finite hFfin
  refine natural_boundary_of_even_fe hc0 hc2 hζ₀norm hrpos hhd hhe hfe hh0 ?_
  intro ζ hζnorm hζball
  have hζq : q.eval ζ ≠ 0 := harc ζ hζnorm hζball
  rw [hq, eval_mul, eval_mul] at hζq
  obtain ⟨hp1, hp3⟩ := mul_ne_zero_iff.mp hζq
  obtain ⟨hpa, hpb⟩ := mul_ne_zero_iff.mp hp1
  exact continuesAcross_of_separable_fibre_disk hhd P ζ hζnorm hpa
    (separable_specialize ζ hpa hpb hp3) hdeg hrel

/-- **The disk model satisfies NO polynomial relation over `ℂ(t)` — full transcendence of `h`.** -/
theorem h_no_relation {h : ℂ → ℂ} {c : ℂ}
    (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ z ∈ ball (0:ℂ) 1, h (-z) = h z)
    (hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2)
    (hh0 : h 0 = 1)
    (P : (Polynomial ℂ)[X]) (hdeg : 1 ≤ P.natDegree)
    (hrel : ∀ t ∈ ball (0:ℂ) 1, P.eval₂ (evalRingHom t) (h t) = 0) : False := by
  classical
  set alg := algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) with halg
  have halginj : Function.Injective alg := IsFractionRing.injective _ _
  have hsmul : ∀ (r : Polynomial ℂ) (p : (FractionRing (Polynomial ℂ))[X]),
      r • p = C (alg r) * p := fun r p => by
    rw [← algebraMap_smul (FractionRing (Polynomial ℂ)) r p, Polynomial.smul_eq_C_mul]
  suffices H : ∀ d : ℕ, ∀ Q : (Polynomial ℂ)[X], Q.natDegree = d → 1 ≤ Q.natDegree →
      (∀ t ∈ ball (0:ℂ) 1, Q.eval₂ (evalRingHom t) (h t) = 0) → False by
    exact H P.natDegree P rfl hdeg hrel
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro Q hQd hQ1 hQrel
    have hQ0 : Q ≠ 0 := fun h' => by rw [h', natDegree_zero] at hQ1; omega
    set Qf := Q.map alg with hQf
    have hQfdeg : Qf.natDegree = Q.natDegree := natDegree_map_eq_of_injective halginj Q
    have hQf0 : Qf ≠ 0 := fun h' => hQ0 ((Polynomial.map_eq_zero_iff halginj).mp h')
    by_cases hirr : Irreducible Qf
    · exact h_separable_no_relation hc0 hc2 hhd hhe hfe hh0 Q hirr.separable hQ1 hQrel
    · have hQf_nu : ¬ IsUnit Qf := fun hu => by
        have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        rw [hQfdeg, hQd] at h0; omega
      obtain ⟨A, B, hAnu, hBnu, hPfAB⟩ := (irreducible_or_factor hQf_nu).resolve_left hirr
      have hA0 : A ≠ 0 := by rintro rfl; rw [zero_mul] at hPfAB; exact hQf0 hPfAB
      have hB0 : B ≠ 0 := by rintro rfl; rw [mul_zero] at hPfAB; exact hQf0 hPfAB
      obtain ⟨bA, hbAmem, hbA⟩ :=
        IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℂ)) A
      obtain ⟨bB, hbBmem, hbB⟩ :=
        IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℂ)) B
      set Atil := IsLocalization.integerNormalization (Polynomial ℂ)⁰ A with hAtil
      set Btil := IsLocalization.integerNormalization (Polynomial ℂ)⁰ B with hBtil
      have hbApoly0 : bA ≠ 0 := nonZeroDivisors.ne_zero hbAmem
      have hbBpoly0 : bB ≠ 0 := nonZeroDivisors.ne_zero hbBmem
      have hbA0 : alg bA ≠ 0 :=
        fun h' => hbApoly0 (halginj (by rw [h', map_zero]))
      have hbB0 : alg bB ≠ 0 :=
        fun h' => hbBpoly0 (halginj (by rw [h', map_zero]))
      have hAtil0 : Atil ≠ 0 := fun h' => hA0
        ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hAtil, h']))
      have hBtil0 : Btil ≠ 0 := fun h' => hB0
        ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hBtil, h']))
      have hdegA : 1 ≤ A.natDegree := by
        rcases Nat.eq_zero_or_pos A.natDegree with h' | h'
        · exfalso; apply hAnu
          rw [Polynomial.eq_C_of_natDegree_eq_zero h']
          refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
          intro hc; apply hA0; rw [Polynomial.eq_C_of_natDegree_eq_zero h', hc, map_zero]
        · exact h'
      have hdegB : 1 ≤ B.natDegree := by
        rcases Nat.eq_zero_or_pos B.natDegree with h' | h'
        · exfalso; apply hBnu
          rw [Polynomial.eq_C_of_natDegree_eq_zero h']
          refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
          intro hc; apply hB0; rw [Polynomial.eq_C_of_natDegree_eq_zero h', hc, map_zero]
        · exact h'
      have hdegAtil : Atil.natDegree = A.natDegree := by
        have h1 := natDegree_map_eq_of_injective halginj Atil
        rw [hbA, hsmul, Polynomial.natDegree_C_mul hbA0] at h1; omega
      have hdegBtil : Btil.natDegree = B.natDegree := by
        have h1 := natDegree_map_eq_of_injective halginj Btil
        rw [hbB, hsmul, Polynomial.natDegree_C_mul hbB0] at h1; omega
      have hdescent : Atil * Btil = C (bA * bB) * Q := by
        apply Polynomial.map_injective alg halginj
        rw [Polynomial.map_mul, hbA, hbB, hsmul, hsmul, Polynomial.map_mul, Polynomial.map_C,
          map_mul alg, Polynomial.C_mul, ← hQf, hPfAB]
        ring
      have hdegsum : Atil.natDegree + Btil.natDegree = d := by
        have hm := Polynomial.natDegree_mul hAtil0 hBtil0
        rw [hdescent, Polynomial.natDegree_C_mul (mul_ne_zero hbApoly0 hbBpoly0), hQd] at hm
        omega
      have heval : ∀ t ∈ ball (0:ℂ) 1, (Atil.eval₂ (evalRingHom t) (h t))
          * (Btil.eval₂ (evalRingHom t) (h t)) = 0 := by
        intro t ht
        rw [← eval₂_mul, hdescent, eval₂_mul, eval₂_C, hQrel t ht, mul_zero]
      rcases analytic_domain_ball (relation_analytic_ball hhd Atil)
          (relation_analytic_ball hhd Btil) heval with hAz | hBz
      · exact IH Atil.natDegree (by omega) Atil rfl (by omega) hAz
      · exact IH Btil.natDegree (by omega) Btil rfl (by omega) hBz

end
end Bottcher
