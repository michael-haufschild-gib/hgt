import GaloisForLFunctions.HTGeometry.FamilyBoundedRelationSurvival

/-!
# Survival against relations with coefficients in a field over which the profile base is transcendental

A source whose Taylor coefficients are the powers `t ^ e i` of one base has, for every atom key,
the single value `t ^ (∑ ν i · e i)`.  If the exponent sequence `e` has bounded-relation
confinement, a full-degree key supported beyond the confinement threshold is alone in its exponent
class.  When `t` is transcendental over a field `K` carrying all the weights, the grouped relation
is a polynomial identity in `t` over `K`, so every grouped coefficient vanishes — in particular the
isolated one, which is a contradiction.

This replaces the Lindemann--Weierstrass separation of `BoundedRelationExponentialSurvival` and
`FamilyBoundedRelationSurvival`, and with it the algebraicity hypotheses on the coefficients and on
the dilations: only membership in `K` is required, and `t` is chosen afterwards.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-! ## Power profiles and their atoms -/

/-- The natural exponent carried by an atom of a power profile. -/
theorem boundedAtomValuation_intCast (e : ℕ → ℕ) (ν : ℕ →₀ ℕ) :
    boundedAtomValuation (fun n => ((e n : ℤ))) ν = ((boundedAtomValuation e ν : ℕ) : ℤ) := by
  classical
  rw [boundedAtomValuation, boundedAtomValuation, Finsupp.sum, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- **The atom of a power profile is a single power of the base.** -/
theorem atomProd_eq_pow_boundedAtomValuation {t : ℂ} {e : ℕ → ℕ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F = t ^ e i) (ν : ℕ →₀ ℕ) :
    ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) = t ^ (boundedAtomValuation e ν) := by
  classical
  rw [Finsupp.prod, boundedAtomValuation, Finsupp.sum,
    ← Finset.prod_pow_eq_pow_sum ν.support (fun i => ν i • e i) t]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hF, ← pow_mul, smul_eq_mul, mul_comm]

/-- Regroup a finite atom sum of a power profile by the exponent of its atom. -/
theorem sum_atomProd_regrouped_by_pow {t : ℂ} {e : ℕ → ℕ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F = t ^ e i)
    (A : Finset (ℕ →₀ ℕ)) (w : (ℕ →₀ ℕ) → ℂ) :
    ∑ ν ∈ A, ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) * w ν =
      ∑ v ∈ A.image (boundedAtomValuation e),
        (∑ ν ∈ A.filter (fun ν => boundedAtomValuation e ν = v), w ν) * t ^ v := by
  classical
  calc
    ∑ ν ∈ A, ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) * w ν =
        ∑ ν ∈ A, t ^ (boundedAtomValuation e ν) * w ν := by
          exact Finset.sum_congr rfl fun ν _ => by
            rw [atomProd_eq_pow_boundedAtomValuation hF]
    _ = ∑ v ∈ A.image (boundedAtomValuation e),
          ∑ ν ∈ A.filter (fun ν => boundedAtomValuation e ν = v),
            t ^ (boundedAtomValuation e ν) * w ν := by
          rw [Finset.sum_fiberwise_of_maps_to (fun ν hν => Finset.mem_image_of_mem _ hν)]
    _ = ∑ v ∈ A.image (boundedAtomValuation e),
          (∑ ν ∈ A.filter (fun ν => boundedAtomValuation e ν = v), w ν) * t ^ v := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun ν hν => ?_
          rw [(Finset.mem_filter.mp hν).2]
          ring

/-! ## The transcendence separation -/

/-- **A vanishing finite power sum in a transcendental base has vanishing coefficients.** -/
theorem eq_zero_of_transcendental_pow_sum {K : Subfield ℂ} {t : ℂ} (ht : Transcendental K t)
    {V : Finset ℕ} {c : ℕ → ℂ} (hc : ∀ v ∈ V, c v ∈ K)
    (h : ∑ v ∈ V, c v * t ^ v = 0) : ∀ v ∈ V, c v = 0 := by
  classical
  obtain ⟨c', hcoe⟩ : ∃ c' : ℕ → ↥K, ∀ v ∈ V, ((c' v : ℂ)) = c v := by
    refine ⟨fun v => if hv : v ∈ V then ⟨c v, hc v hv⟩ else 0, fun v hv => ?_⟩
    simp only [dif_pos hv]
  set P : Polynomial ↥K := ∑ v ∈ V, Polynomial.monomial v (c' v) with hP
  have haeval : Polynomial.aeval t P = 0 := by
    rw [hP, map_sum, ← h]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Polynomial.aeval_monomial]
    show ((c' v : ℂ)) * t ^ v = c v * t ^ v
    rw [hcoe v hv]
  have hPzero : P = 0 := by
    by_contra hne
    exact ht ⟨P, hne, haeval⟩
  intro v hv
  have hcoeff : P.coeff v = c' v := by
    rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single v]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro u _ hu
      rw [Polynomial.coeff_monomial, if_neg hu]
    · intro hvV
      exact absurd hv hvV
  have hzero : c' v = 0 := by rw [← hcoeff, hPzero, Polynomial.coeff_zero]
  rw [← hcoe v hv, hzero, ZeroMemClass.coe_zero]

/-! ## Membership of the family weights -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem famWeight_mem {n : ℕ} {K : Subfield ℂ} (q : ι → ℂ) (hqK : ∀ i, q i ∈ K)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ) :
    famWeight q n m l ∈ K := by
  classical
  rw [famWeight]
  refine Subfield.prod_mem _ fun t _ => ?_
  exact mul_mem (natCast_mem K _) (pow_mem (hqK _) _)

omit [DecidableEq ι] [Nonempty ι] in
theorem famAevalWeight_mem {n N : ℕ} {K : Subfield ℂ} (q : ι → ℂ) (hqK : ∀ i, q i ∈ K)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    (hQK : ∀ m, MvPolynomial.coeff m Q ∈ K) (ν : ℕ →₀ ℕ) :
    famAevalWeight q n N Q ν ∈ K := by
  classical
  rw [famAevalWeight]
  exact Subfield.sum_mem _ fun x _ => mul_mem (hQK _) (famWeight_mem q hqK _ _)

/-! ## The survival theorem -/

/-- **A dilated family of one power-profile source defeats every jet relation whose coefficients,
together with the dilations, lie in a field over which the base is transcendental.** -/
theorem exists_coeff_ne_zero_famJets_of_transcendentalProfile
    {K : Subfield ℂ} {t : ℂ} {e : ℕ → ℕ} {H : PowerSeries ℂ} (q : ι → ℂ)
    (hH : ∀ i, PowerSeries.coeff i H = t ^ e i)
    (ht : Transcendental K t)
    (hconf : BoundedRelationConfinement (fun n => ((e n : ℤ))))
    (hq0 : ∀ i, q i ≠ 0) (hqinj : Function.Injective q) (hqK : ∀ i, q i ∈ K)
    {n : ℕ} (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    (hQK : ∀ m, MvPolynomial.coeff m Q ∈ K) (hQ : Q ≠ 0) :
    ∃ N, PowerSeries.coeff N
      (MvPolynomial.aeval (familyJets n (fun i => rescale (q i) H)) Q) ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := hconf (famMaxSlotCount Q)
  have hsupport : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQ
  obtain ⟨m₀, hm₀, hsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupport
      (fun m => ∑ p : ι × Fin (n + 1), m (some p))
  have hcount₀ : (∑ p : ι × Fin (n + 1), m₀ (some p)) = famMaxSlotCount Q := by
    rw [famMaxSlotCount]
    exact hsup.symm
  obtain ⟨k, hkn, hkinj, hw⟩ :=
    exists_key_famAevalWeight_ne_zero_of_mem q hq0 hqinj (le_max_left n M) Q hm₀
  set N : ℕ := keyTrunc n m₀ k with hN
  set A : Finset (ℕ →₀ ℕ) := (famSigmaIdx n N Q).image (famAtomKey n) with hA
  have hstarMem : key k ∈ A := by
    by_contra hno
    refine hw ?_
    rw [famAevalWeight]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxmem, hxkey⟩ := Finset.mem_filter.mp hx
    exact absurd (hA ▸ Finset.mem_image_of_mem (famAtomKey n) hxmem) (hxkey ▸ hno)
  have hstarCount : (key k).sum (fun _ v => v) = famMaxSlotCount Q := by
    rw [key_total_count, hcount₀]
  have hstarTail : ∀ i, (key k) i ≠ 0 → M ≤ i := by
    intro i hi
    have hex : ∃ s, k s = i := by
      by_contra hno
      refine hi ?_
      rw [key_apply]
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_)
      exact hno ⟨s, (Finset.mem_filter.mp hs).2⟩
    obtain ⟨s, rfl⟩ := hex
    have := hkn s
    have hle : M ≤ max n M := le_max_right n M
    omega
  have hstarUnique : ∀ μ ∈ A,
      boundedAtomValuation e μ = boundedAtomValuation e (key k) → μ = key k := by
    intro μ hμ hval
    refine atom_eq_of_valuation_eq_of_full_tail hM hstarCount
      (famAppearing_atom_count_le Q hμ) hstarTail ?_
    rw [boundedAtomValuation_intCast, boundedAtomValuation_intCast, hval]
  refine ⟨N, ?_⟩
  intro hcoeff
  have hsumzero : ∑ ν ∈ A,
      ν.prod (fun i j => (PowerSeries.coeff i H) ^ j) * famAevalWeight q n N Q ν = 0 := by
    rw [← coeff_aeval_famJets_regrouped n N q H Q]
    exact hcoeff
  have hgroupzero :
      ∑ v ∈ A.image (boundedAtomValuation e),
          (∑ ν ∈ A.filter (fun ν => boundedAtomValuation e ν = v),
            famAevalWeight q n N Q ν) * t ^ v = 0 := by
    rw [← sum_atomProd_regrouped_by_pow hH A (famAevalWeight q n N Q)]
    exact hsumzero
  have hallzero := eq_zero_of_transcendental_pow_sum ht
    (V := A.image (boundedAtomValuation e))
    (c := fun v => ∑ ν ∈ A.filter (fun ν => boundedAtomValuation e ν = v),
      famAevalWeight q n N Q ν)
    (fun v _ => Subfield.sum_mem _ fun ν _ => famAevalWeight_mem q hqK Q hQK ν)
    hgroupzero
  have hvstar : boundedAtomValuation e (key k) ∈ A.image (boundedAtomValuation e) :=
    Finset.mem_image.mpr ⟨key k, hstarMem, rfl⟩
  have hfiber :
      A.filter (fun μ => boundedAtomValuation e μ = boundedAtomValuation e (key k)) = {key k} := by
    ext μ
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hh => hstarUnique μ hh.1 hh.2, fun hh => by rw [hh]; exact ⟨hstarMem, rfl⟩⟩
  have hzero := hallzero _ hvstar
  rw [hfiber, Finset.sum_singleton] at hzero
  exact hw hzero

end

end GaloisForLFunctions
