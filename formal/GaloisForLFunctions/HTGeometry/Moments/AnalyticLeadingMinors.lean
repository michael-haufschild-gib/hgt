import GaloisForLFunctions.HTGeometry.Moments.PolynomialLeadingMinors
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum
import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure

/-!
# Leading derivative Hankel minors and differential order

For an analytic germ, leading Hankel determinants of its derivatives vanish above
size `B` exactly when a nonzero constant-coefficient differential operator of order
at most `B` annihilates the germ. The last nonzero leading block gives the exact
minimum order. Exponential-polynomial germs are characterized by analyticity and
this determinant cutoff; for entire functions, the characterization is global.
-/

open Filter Topology
open scoped BigOperators
open _root_.HTGeometry.FiniteHankel

namespace GaloisForLFunctions.HTGeometry

/-- A constant-coefficient response recurrence is detected by eventual leading-determinant vanishing. -/
theorem seqConstantRecurrence_iff_leading_tail (s : ℕ → ℂ) :
    SeqConstantRecurrence s ↔ ∃ B, ∀ n, B < n → leadingDet s n = 0 := by
  constructor
  · rintro ⟨p, hp, hrec⟩
    exact ⟨p.natDegree, (leading_tail_zero_iff_polynomial_relation s p.natDegree).mpr
      ⟨p, hp, le_rfl, hrec⟩⟩
  · rintro ⟨B, hB⟩
    obtain ⟨p, hp, _, hrec⟩ := (leading_tail_zero_iff_polynomial_relation s B).mp hB
    exact ⟨p, hp, hrec⟩

/-- The same polynomial annihilates the derivative sequence and the analytic germ. -/
theorem polynomial_response_relation_iff_localODE {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (p : Polynomial ℂ) :
    (∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * respSeq f (n + k) = 0) ↔
      ∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree f z = 0 := by
  constructor
  · intro hrec
    apply _root_.HTGeometry.eventuallyEq_zero_of_iteratedDeriv_eq_zero
      (analyticAt_odeSum hf _ _)
    intro n
    rw [iteratedDeriv_odeSum_zero hf]
    exact hrec n
  · intro hode n
    have hev : odeSum p.coeff p.natDegree f =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := hode
    have he := EventuallyEq.iteratedDeriv_eq n hev
    rw [iteratedDeriv_odeSum_zero hf] at he
    simpa using he

/-- For an entire response, the polynomial differential equation holds on the whole plane. -/
theorem polynomial_response_relation_iff_globalODE {f : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (p : Polynomial ℂ) :
    (∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * respSeq f (n + k) = 0) ↔
      ∀ z, odeSum p.coeff p.natDegree f z = 0 := by
  constructor
  · intro hrec
    have hnear := (polynomial_response_relation_iff_localODE (hf 0) p).mp hrec
    have hAna : AnalyticOnNhd ℂ (odeSum p.coeff p.natDegree f) Set.univ :=
      fun z _ => analyticAt_odeSum (hf z) _ _
    exact fun z => hAna.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) hnear (Set.mem_univ z)
  · intro h
    exact (polynomial_response_relation_iff_localODE (hf 0) p).mpr
      (Filter.Eventually.of_forall h)

/-- The determinant cutoff and local differential-operator degree have the same bound. -/
theorem leading_tail_zero_respSeq_iff_localODE {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (B : ℕ) :
    (∀ n, B < n → leadingDet (respSeq f) n = 0) ↔
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ p.natDegree ≤ B ∧
        ∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree f z = 0 := by
  rw [leading_tail_zero_iff_polynomial_relation]
  constructor
  · rintro ⟨p, hp, hpB, hrec⟩
    exact ⟨p, hp, hpB, (polynomial_response_relation_iff_localODE hf p).mp hrec⟩
  · rintro ⟨p, hp, hpB, hode⟩
    exact ⟨p, hp, hpB, (polynomial_response_relation_iff_localODE hf p).mpr hode⟩

/-- An exponential-polynomial germ is analytic at its center. -/
theorem analyticAt_of_germExpPoly {f : ℂ → ℂ} (h : GermExpPoly f) :
    AnalyticAt ℂ f 0 := by
  obtain ⟨G, hG, hfG⟩ := h
  exact (analyticAt_of_mem_expPolySpaceC hG 0).congr hfG.symm

/-- Exact characterization of exponential-polynomial germs among all complex functions. -/
theorem germExpPoly_iff_analytic_leading_tail (f : ℂ → ℂ) :
    GermExpPoly f ↔ AnalyticAt ℂ f 0 ∧
      ∃ B, ∀ n, B < n → leadingDet (respSeq f) n = 0 := by
  constructor
  · intro h
    have hf := analyticAt_of_germExpPoly h
    obtain ⟨p, hp, hode⟩ := germConstantODE_of_germExpPoly h
    exact ⟨hf, p.natDegree, (leading_tail_zero_respSeq_iff_localODE hf p.natDegree).mpr
      ⟨p, hp, le_rfl, hode⟩⟩
  · rintro ⟨hf, B, hB⟩
    obtain ⟨p, hp, _, hode⟩ := (leading_tail_zero_respSeq_iff_localODE hf B).mp hB
    exact germExpPoly_of_germConstantODE hf ⟨p, hp, hode⟩

/-- The last nonsingular derivative Hankel block is the minimum local ODE order. -/
theorem localODE_minimalDegree_of_last_leading_det {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (m : ℕ)
    (hm : leadingDet (respSeq f) m ≠ 0)
    (htail : ∀ n, m < n → leadingDet (respSeq f) n = 0) :
    (∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree = m ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree f z = 0) ∧
    (∀ p : Polynomial ℂ, p ≠ 0 →
      (∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree f z = 0) → m ≤ p.natDegree) := by
  constructor
  · obtain ⟨p, hp, hdeg, hrec⟩ := monic_relation_of_last_leading_det (respSeq f) m hm htail
    exact ⟨p, hp, hdeg, (polynomial_response_relation_iff_localODE hf p).mp hrec⟩
  · intro p hp hode
    exact leading_nonzero_le_relation_degree (respSeq f) m hm p hp
      ((polynomial_response_relation_iff_localODE hf p).mpr hode)

/-- An entire function with an exponential-polynomial germ is globally that exponential polynomial. -/
theorem mem_expPolySpaceC_of_entire_germExpPoly {f : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (h : GermExpPoly f) : f ∈ expPolySpaceC := by
  obtain ⟨G, hG, hfG⟩ := h
  have hAna : AnalyticOnNhd ℂ (fun z => f z - G z) Set.univ :=
    fun z _ => (hf z).sub (analyticAt_of_mem_expPolySpaceC hG z)
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), f z - G z = 0 :=
    hfG.mono fun z hz => sub_eq_zero.mpr hz
  have he : f = G := by
    funext z
    exact sub_eq_zero.mp (hAna.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) hnear (Set.mem_univ z))
  rwa [he]

/-- Exact global characterization by entireness and a leading-determinant cutoff. -/
theorem mem_expPolySpaceC_iff_entire_leading_tail (f : ℂ → ℂ) :
    f ∈ expPolySpaceC ↔ (∀ z, AnalyticAt ℂ f z) ∧
      ∃ B, ∀ n, B < n → leadingDet (respSeq f) n = 0 := by
  constructor
  · intro h
    have hg : GermExpPoly f := ⟨f, h, Filter.EventuallyEq.refl _ _⟩
    exact ⟨analyticAt_of_mem_expPolySpaceC h, (germExpPoly_iff_analytic_leading_tail f).mp hg |>.2⟩
  · rintro ⟨hf, ht⟩
    exact mem_expPolySpaceC_of_entire_germExpPoly hf
      ((germExpPoly_iff_analytic_leading_tail f).mpr ⟨hf 0, ht⟩)

#print axioms mem_expPolySpaceC_iff_entire_leading_tail
#print axioms germExpPoly_iff_analytic_leading_tail
#print axioms localODE_minimalDegree_of_last_leading_det

end GaloisForLFunctions.HTGeometry
