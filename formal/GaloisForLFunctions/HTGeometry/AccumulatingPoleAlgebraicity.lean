import GaloisForLFunctions.HTGeometry.InverseGammaPoleCluster
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Accumulating poles obstruct local meromorphic algebraicity

This module supplies the local algebraicity criterion needed by the inverse-Gamma pole-cluster
card.  A polynomial relation with meromorphic coefficient germs is normalized at each satellite
pole; the nonzero residue forces its leading coefficient to vanish.  Accumulation at the base
point then contradicts isolated zeros for a nonzero meromorphic germ.
-/


namespace GaloisForLFunctions

open Complex Filter Topology Set

/-- A polynomial relation for `f` near `a`, with coefficients meromorphic at `a` and a nonzero
leading coefficient germ.  This is the function-level presentation of algebraicity over the local
meromorphic germ field. -/
def LocallyMeromorphicallyAlgebraicAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ) (U : Set ℂ),
    IsOpen U ∧ a ∈ U ∧
    (∀ j, MeromorphicAt (A j) a) ∧
    ¬((A ⟨d, Nat.lt_succ_self d⟩) =ᶠ[nhdsWithin a {a}ᶜ] (fun _ => 0)) ∧
    ∀ z ∈ U, f z ≠ 0 → ∑ j, A j z * f z ^ (j : ℕ) = 0

theorem leadingCoeff_eq_zero_of_residue_pole_relation
    {f : ℂ → ℂ} {c ρ : ℂ} {d : ℕ} {A : Fin (d + 1) → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hcU : c ∈ U) (hAan : ∀ j, AnalyticAt ℂ (A j) c)
    (hrel : ∀ z ∈ U, f z ≠ 0 → ∑ j, A j z * f z ^ (j : ℕ) = 0)
    (hρ : ρ ≠ 0)
    (hpole : Tendsto (fun z : ℂ => (z - c) * f z)
      (nhdsWithin c {c}ᶜ) (nhds ρ)) :
    A ⟨d, Nat.lt_succ_self d⟩ c = 0 := by
  have hprodNe : ∀ᶠ z in nhdsWithin c {c}ᶜ, (z - c) * f z ≠ 0 :=
    hpole.eventually_ne hρ
  have hfne : ∀ᶠ z in nhdsWithin c {c}ᶜ, f z ≠ 0 := by
    filter_upwards [hprodNe] with z hz
    exact fun hf => hz (by rw [hf, mul_zero])
  have hnum : Tendsto (fun z : ℂ => z - c) (nhdsWithin c {c}ᶜ) (nhds 0) := by
    have h : Tendsto (fun z : ℂ => z - c) (nhds c) (nhds 0) := by
      have h' := (tendsto_id : Tendsto (id : ℂ → ℂ) (nhds c) (nhds c)).sub_const c
      simpa using h'
    exact h.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun z : ℂ => (f z)⁻¹) (nhdsWithin c {c}ᶜ) (nhds 0) := by
    have hquot := hnum.div hpole hρ
    simpa [hρ] using hquot.congr' (by
      filter_upwards [hprodNe, self_mem_nhdsWithin] with z hprod hz
      have hzc : z - c ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_ne_zero] using hz
      have hfz : f z ≠ 0 := fun hf => hprod (by rw [hf, mul_zero])
      change (z - c) / ((z - c) * f z) = (f z)⁻¹
      field_simp [hzc, hfz])
  let F : ℂ → ℂ := fun z => ∑ j, A j z * (f z)⁻¹ ^ (d - (j : ℕ))
  have hFtend : Tendsto F (nhdsWithin c {c}ᶜ)
      (nhds (A ⟨d, Nat.lt_succ_self d⟩ c)) := by
    have hsum := tendsto_finsetSum (s := Finset.univ) (fun j _ =>
      ((hAan j).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        (hinv.pow (d - (j : ℕ))))
    convert hsum using 1
    rw [Finset.sum_eq_single ⟨d, Nat.lt_succ_self d⟩]
    · simp
    · intro j _ hj
      have hjlt : (j : ℕ) < d := by
        have hjle : (j : ℕ) ≤ d := by omega
        exact lt_of_le_of_ne hjle (by
          intro hEq
          apply hj
          exact Fin.ext hEq)
      have hsub : d - (j : ℕ) ≠ 0 := by omega
      rw [zero_pow hsub, mul_zero]
    · simp
  have hFzero : ∀ᶠ z in nhdsWithin c {c}ᶜ, F z = 0 := by
    filter_upwards [hfne, eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hcU)]
      with z hfz hzU
    have hrelation := hrel z hzU hfz
    change (∑ j, A j z * (f z)⁻¹ ^ (d - (j : ℕ))) = 0
    calc
      (∑ j, A j z * (f z)⁻¹ ^ (d - (j : ℕ))) =
          (f z)⁻¹ ^ d * ∑ j, A j z * f z ^ (j : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hjle : (j : ℕ) ≤ d := by omega
        have hpow : (f z)⁻¹ ^ (d - (j : ℕ)) =
            (f z)⁻¹ ^ d * f z ^ (j : ℕ) := by
          rw [inv_pow, inv_pow, pow_sub₀ _ hfz hjle, mul_inv, inv_inv]
        rw [hpow]
        ring
      _ = 0 := by rw [hrelation, mul_zero]
  have hzero : Tendsto F (nhdsWithin c {c}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' (hFzero.mono fun _ hz => hz.symm)
  exact tendsto_nhds_unique hFtend hzero

/-- A sequence of nonzero-residue poles accumulating at `a` rules out every polynomial relation
whose coefficients are meromorphic at `a` and whose leading coefficient is a nonzero germ. -/
theorem not_locallyMeromorphicallyAlgebraicAt_of_accumulating_residue_poles
    {f : ℂ → ℂ} {a : ℂ} {c ρ : ℕ → ℂ}
    (hc : Tendsto c atTop (nhdsWithin a {a}ᶜ))
    (hpoles : ∀ᶠ m : ℕ in atTop,
      ρ m ≠ 0 ∧ Tendsto (fun z : ℂ => (z - c m) * f z)
        (nhdsWithin (c m) {c m}ᶜ) (nhds (ρ m))) :
    ¬LocallyMeromorphicallyAlgebraicAt f a := by
  rintro ⟨d, A, U, hU, haU, hAmer, hlead, hrel⟩
  have hAan : ∀ᶠ z in nhdsWithin a {a}ᶜ, ∀ j, AnalyticAt ℂ (A j) z := by
    rw [Filter.eventually_all]
    intro j
    exact (hAmer j).eventually_analyticAt
  have hcentersU : ∀ᶠ m : ℕ in atTop, c m ∈ U :=
    hc.eventually (eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds haU))
  have hzeros : ∀ᶠ m : ℕ in atTop, A ⟨d, Nat.lt_succ_self d⟩ (c m) = 0 := by
    filter_upwards [hpoles, hc.eventually hAan, hcentersU] with m hm hAanM hcU
    exact leadingCoeff_eq_zero_of_residue_pole_relation hU hcU hAanM hrel hm.1 hm.2
  rcases (hAmer ⟨d, Nat.lt_succ_self d⟩).eventually_eq_zero_or_eventually_ne_zero with
    hzero | hne
  · exact hlead hzero
  · have hneseq := hc.eventually hne
    have hfalse : ∀ᶠ m : ℕ in atTop, False :=
      (hzeros.and hneseq).mono fun _ hm => hm.2 hm.1
    exact hfalse.exists.elim fun _ h => h

/-- The composite `digamma ∘ Gamma` is not algebraic even over the full field of functions
meromorphic at a negative integer.  In particular it is transcendental over the smaller local
field generated by `z` and `digamma z`. -/
theorem ReciprocalGammaPoleBranch.digamma_comp_Gamma_not_locallyMeromorphicallyAlgebraic
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    ¬LocallyMeromorphicallyAlgebraicAt
      (fun z : ℂ => Complex.digamma (Complex.Gamma z)) (-(n : ℂ)) := by
  let c : ℕ → ℂ := fun m => zn ((m : ℂ)⁻¹)
  let ρ : ℕ → ℂ := fun m => inverseGammaBranchResidueInterpolation zn ((m : ℂ)⁻¹)
  have hcNhds : Tendsto c atTop (nhds (-(n : ℂ))) := by
    have h := zn.analyticAt_zero.continuousAt.tendsto.comp tendsto_natCast_inv_complex
    simpa [c, zn.map_zero] using h
  have hcNe : ∀ᶠ m : ℕ in atTop, c m ∈ ({-(n : ℂ)}ᶜ : Set ℂ) := by
    filter_upwards [zn.factorial_cluster_eventually,
      eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hmCluster hm
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcenter
    have hzero : Complex.Gamma (c m) = 0 := by
      rw [hcenter, Complex.Gamma_neg_nat_eq_zero]
    rw [hzero] at hmCluster
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    exact hm0 (by linear_combination hmCluster.1)
  have hc : Tendsto c atTop (nhdsWithin (-(n : ℂ)) {-(n : ℂ)}ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨hcNhds, hcNe⟩
  have hpoles : ∀ᶠ m : ℕ in atTop,
      ρ m ≠ 0 ∧ Tendsto
        (fun z : ℂ => (z - c m) * Complex.digamma (Complex.Gamma z))
        (nhdsWithin (c m) {c m}ᶜ) (nhds (ρ m)) := by
    simpa [c, ρ] using zn.factorial_cluster_eventually.mono fun _ hm => ⟨hm.2.1, hm.2.2⟩
  exact not_locallyMeromorphicallyAlgebraicAt_of_accumulating_residue_poles hc hpoles

end GaloisForLFunctions
