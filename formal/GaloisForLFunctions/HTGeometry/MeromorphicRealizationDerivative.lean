import GaloisForLFunctions.HTGeometry.MeromorphicFractionRealization

/-!
# Realization commutes with differentiation

A meromorphic germ presented as a fraction of entire germs has a derivative presented by the
quotient rule, and the function realizing it has the ordinary derivative of that fraction wherever
the denominator is nonzero.  So realization is compatible with the derivation on both sides, and
therefore with all jets.

* `differential_deriv_div` — the quotient rule in a differential field;
* `realizesMero_deriv`, `realizesMero_iteratedDeriv`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- The Leibniz rule for the derivation of a differential ring. -/
theorem differential_deriv_mul {K : Type*} [CommRing K] [Differential K] (a b : K) :
    (a * b)′ = a′ * b + a * b′ := by
  have h := (Differential.deriv (R := K)).leibniz a b
  simp only [smul_eq_mul] at h
  rw [h]
  ring

/-- **The quotient rule in a differential field.** -/
theorem differential_deriv_div {K : Type*} [Field K] [Differential K] (a b : K) (hb : b ≠ 0) :
    (a / b)′ = (a′ * b - a * b′) / b ^ 2 := by
  have hbb : b * (a / b) = a := by field_simp
  have hd : (b * (a / b))′ = a′ := by rw [hbb]
  rw [differential_deriv_mul] at hd
  set t := (a / b)′ with ht
  rw [eq_div_iff (pow_ne_zero 2 hb)]
  field_simp at hd
  linear_combination hd

/-- An entire function as an element of the global analytic germ domain. -/
def entireElem (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ)) :
    analyticSubring (Set.univ : Set ℂ) :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) A, ⟨A, hA, rfl⟩⟩

theorem entireElem_coe (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ)) :
    ((entireElem A hA : analyticSubring (Set.univ : Set ℂ)) : Germ (𝓟 Set.univ) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) A := rfl

theorem analyticSubringDeriv_entireElem (A : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ)) :
    analyticSubringDeriv isOpen_univ (entireElem A hA) = entireElem (deriv A) hA.deriv := rfl

/-- Realization by an explicit fraction of entire functions. -/
theorem realizesMero_fraction {A B f : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ))
    (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ)) (hB0 : entireElem B hB ≠ 0)
    (hf : ∀ z, B z ≠ 0 → f z = A z / B z) :
    RealizesMero (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem A hA) /
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem B hB)) f :=
  ⟨entireElem A hA, entireElem B hB, A, B, hB0, hA, hB, rfl, rfl, rfl, hf⟩

/-- **Realization commutes with the derivation.** -/
theorem realizesMero_deriv {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (h : RealizesMero x f) :
    letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
    RealizesMero (x′) (deriv f) := by
  letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := h
  -- replace the abstract germs by the entire representatives
  have ha : a = entireElem A hA := Subtype.ext hAa.symm
  have hb : b = entireElem B hB := Subtype.ext hBb.symm
  subst ha
  subst hb
  have hbne : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (entireElem B hB) ≠ 0 := algebraMap_analyticSubring_ne_zero hb0
  have hderivA : (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (entireElem A hA))′ = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem (deriv A) hA.deriv) := by
    rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ Set.univ_nonempty,
      analyticSubringDeriv_entireElem]
  have hderivB : (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (entireElem B hB))′ = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem (deriv B) hB.deriv) := by
    rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ Set.univ_nonempty,
      analyticSubringDeriv_entireElem]
  have hnum : AnalyticOnNhd ℂ (fun z ↦ deriv A z * B z - A z * deriv B z)
      (Set.univ : Set ℂ) := (hA.deriv.mul hB).sub (hA.mul hB.deriv)
  have hden : AnalyticOnNhd ℂ (fun z ↦ B z * B z) (Set.univ : Set ℂ) := hB.mul hB
  have hden0 : entireElem (fun z ↦ B z * B z) hden ≠ 0 := by
    intro hzero
    apply hb0
    have hmul : entireElem (fun z ↦ B z * B z) hden = entireElem B hB * entireElem B hB := rfl
    rw [hmul, mul_self_eq_zero] at hzero
    exact hzero
  have hxeq : (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
        (entireElem A hA) /
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem B hB))′
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ deriv A z * B z - A z * deriv B z) hnum) /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ B z * B z) hden) := by
    rw [differential_deriv_div _ _ hbne, hderivA, hderivB]
    have hnumeq : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ deriv A z * B z - A z * deriv B z) hnum)
        = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
            (entireElem (deriv A) hA.deriv)
          * algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem B hB)
          - algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (entireElem A hA)
            * algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
              (entireElem (deriv B) hB.deriv) := by
      rw [← map_mul, ← map_mul, ← map_sub]
      rfl
    have hdeneq : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
          (entireElem (fun z ↦ B z * B z) hden)
        = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
            (entireElem B hB) ^ 2 := by
      rw [pow_two, ← map_mul]
      rfl
    rw [hnumeq, hdeneq]
  rw [hxab, hxeq]
  refine realizesMero_fraction hnum hden hden0 fun z hz ↦ ?_
  -- the function agrees with the fraction near `z`, so its derivative is the quotient rule
  have hBz : B z ≠ 0 := by
    intro hzero
    exact hz (by rw [hzero, mul_zero])
  have hev : f =ᶠ[𝓝 z] fun w ↦ A w / B w := by
    have hcont : ContinuousAt B z := (hB z (Set.mem_univ z)).continuousAt
    filter_upwards [hcont.eventually_ne hBz] with w hw
    exact hfAB w hw
  rw [hev.deriv_eq, deriv_fun_div ((hA z (Set.mem_univ z)).differentiableAt)
    ((hB z (Set.mem_univ z)).differentiableAt) hBz]
  field_simp
  ring

/-- **Realization commutes with all jets.** -/
theorem realizesMero_iteratedDeriv {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (h : RealizesMero x f) (j : ℕ) :
    letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
    RealizesMero (differentialJet j x) (iteratedDeriv j f) := by
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  induction j with
  | zero =>
      have hjet : differentialJet 0 x = x := differentialJet_zero x
      have hfun : iteratedDeriv 0 f = f := iteratedDeriv_zero
      rw [hjet, hfun]
      exact h
  | succ n ih =>
      have hjet : differentialJet (n + 1) x = (differentialJet n x)′ := by
        rw [differentialJet_succ]
      have hfun : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := iteratedDeriv_succ
      rw [hjet, hfun]
      exact realizesMero_deriv ih

end

end GaloisForLFunctions.HTGeometry
