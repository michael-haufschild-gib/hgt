import GaloisForLFunctions.RHTower.XiGaussianHeatEscapingBranches
import GaloisForLFunctions.HTGeometry.AnalyticEscapingFactorization

/-!
# The exact finite factor of an actual HCF admission

Removing the known escaping packet leaves a monic polynomial with analytic
coefficients through the contact. Its value is exactly the preceding regular
head's admission, with all finite-root multiplicities retained. The result
uses only positive time and rank; the finite roots need not be simple.
-/

open Filter Topology Polynomial HTGeometry GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- Package the known coefficientwise cancellation as an analytic polynomial. -/
theorem heat_normal_block_scaled_admission_polynomial (a : {t : ℝ // 0 < t})
    {n d k : ℕ} (hblock : MomentNormalBlock (heatRealMoments a) n d) (hk : k < d) :
    ∃ S : ℝ → ℂ[X], (∀ i, AnalyticAt ℝ (fun t => (S t).coeff i) a) ∧
      S a = C (((d - 1).descFactorial k : ℕ) : ℂ) *
        (monicMomentAdmissionPolynomial (heatRealMoments a) n).map (algebraMap ℝ ℂ) ∧
      (∀ᶠ t in 𝓝[≠] (a : ℝ), S t = C (((t - a : ℝ) : ℂ) ^ k) *
        (monicMomentAdmissionPolynomial (heatRealMoments t) (n + k)).map (algebraMap ℝ ℂ)) := by
  classical
  have hc (i : Fin (n + k + 1)) := heat_normal_block_admission_continuation a hblock k hk i
  choose u hu hua hue using hc
  let S : ℝ → ℂ[X] := fun t => ofFn (n + k + 1) (fun i => (u i t : ℂ))
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i < n + k + 1
    · simp only [S, ofFn_coeff_eq_val_of_lt _ hi]
      exact (Complex.ofRealCLM.analyticAt _).comp (hu ⟨i, hi⟩)
    · simp only [S, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
      exact analyticAt_const
  · ext i
    by_cases hi : i < n + k + 1
    · simp only [S, ofFn_coeff_eq_val_of_lt _ hi]
      rw [coeff_C_mul, coeff_map, Complex.coe_algebraMap,
        hua ⟨i, hi⟩]
      simp only [Complex.ofReal_mul, Complex.ofReal_natCast, heatAdmissionCoeff]
    · simp only [S, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
      rw [coeff_C_mul, coeff_map,
        coeff_eq_zero_of_natDegree_lt (by rw [monicMomentAdmissionPolynomial_natDegree]; omega)]
      simp
  · filter_upwards [Filter.eventually_all.mpr hue] with t ht
    ext i
    by_cases hi : i < n + k + 1
    · simp only [S, ofFn_coeff_eq_val_of_lt _ hi]
      rw [coeff_C_mul, coeff_map, Complex.coe_algebraMap]
      have he := congrArg (fun x : ℝ => (x : ℂ)) (ht ⟨i, hi⟩)
      simpa only [Complex.ofReal_mul, Complex.ofReal_pow, heatAdmissionCoeff] using he.symm
    · simp only [S, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
      rw [coeff_C_mul, coeff_map,
        coeff_eq_zero_of_natDegree_lt (by rw [monicMomentAdmissionPolynomial_natDegree]; omega)]
      simp

/-- Every actual admission has an exact analytic finite/escaping factorization.
The monic finite factor specializes to the regular-head admission even when
that polynomial has multiple roots. -/
theorem hcf_heat_admission_finite_factor (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      ∃ (b : ∀ z : (heatEscapePolynomial (heatRegularGap a j)
          (N - heatRegularHead a j)).rootSet ℂ, HeatAdmissionEscapingBranch a N z)
        (F S : ℝ → ℂ[X]),
        (∀ t, (F t).Monic ∧ (F t).natDegree = heatRegularHead a j) ∧
        (∀ i, AnalyticAt ℝ (fun t => (F t).coeff i) a) ∧
        F a = (monicMomentAdmissionPolynomial (heatRealMoments a)
          (heatRegularHead a j)).map (algebraMap ℝ ℂ) ∧
        (∀ i, AnalyticAt ℝ (fun t => (S t).coeff i) a) ∧
        S a = C (((heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) : ℕ) : ℂ) *
          F a ∧
        (∀ᶠ t in 𝓝[≠] (a : ℝ),
          (monicMomentAdmissionPolynomial (heatRealMoments t) N).map (algebraMap ℝ ℂ) =
            escapingRootFactor (fun z => (b z).scaledRoot) a t * F t) ∧
        (∀ᶠ t in 𝓝[≠] (a : ℝ), S t = C (((t - a : ℝ) : ℂ) ^ (N - heatRegularHead a j)) *
          (monicMomentAdmissionPolynomial (heatRealMoments t) N).map (algebraMap ℝ ℂ)) ∧
        (∀ᶠ t in 𝓝 (a : ℝ),
          S t = scaledEscapingRootFactor (fun z => (b z).scaledRoot) a t * F t) := by
  classical
  obtain ⟨j, hj, hj1, hcard, b, hb⟩ := hcf_heat_admission_escape_packet a N
  have hgap := heatRegularHead_add_gap a j
  have hk : N - heatRegularHead a j < heatRegularGap a j := by omega
  have hnk : heatRegularHead a j + (N - heatRegularHead a j) = N := by omega
  obtain ⟨S, hS, hSa, hscale⟩ := heat_normal_block_scaled_admission_polynomial a
    (heatRegularGap_normalBlock a j) hk
  rw [hnk] at hscale
  let p : ℝ → ℂ[X] := fun t =>
    (monicMomentAdmissionPolynomial (heatRealMoments t) N).map (algebraMap ℝ ℂ)
  have hp (t : ℝ) : (p t).Monic ∧ (p t).natDegree =
      heatRegularHead a j + (N - heatRegularHead a j) := by
    have hm := monicMomentAdmissionPolynomial_monic (heatRealMoments t) N
    refine ⟨hm.map _, ?_⟩
    dsimp only [p]
    rw [hm.natDegree_map, monicMomentAdmissionPolynomial_natDegree, hnk]
  have hroot : ∀ᶠ t in 𝓝[≠] (a : ℝ),
      (∀ z, (p t).eval ((b z).scaledRoot t / ((t - a : ℝ) : ℂ)) = 0) ∧
      Function.Injective (fun z => (b z).scaledRoot t / ((t - a : ℝ) : ℂ)) := by
    simpa only [p, eval_map_algebraMap] using hb
  obtain ⟨F, hFm, hFa, hPF, hSF, hcontact⟩ := analytic_finite_factor_of_escaping_roots
    hcard hp hS hscale (fun z => (b z).analytic)
    (fun z => (b z).at_contact.trans_ne (b z).residue_ne_zero) hroot
  let q := (monicMomentAdmissionPolynomial (heatRealMoments a)
    (heatRegularHead a j)).map (algebraMap ℝ ℂ)
  have hqm : q.Monic := (monicMomentAdmissionPolynomial_monic _ _).map _
  have hqdeg : q.natDegree = heatRegularHead a j := by
    dsimp only [q]
    rw [(monicMomentAdmissionPolynomial_monic _ _).natDegree_map,
      monicMomentAdmissionPolynomial_natDegree]
  have heq : C (((heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) : ℕ) : ℂ) * q =
      C (∏ z, -(b z).scaledRoot a) * F a := hSa.symm.trans hcontact
  have hconstants : (((heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) : ℕ) : ℂ) =
      ∏ z, -(b z).scaledRoot a := by
    have hh := congrArg (fun P : ℂ[X] => P.coeff (heatRegularHead a j)) heq
    have hqc : q.coeff (heatRegularHead a j) = 1 := by
      rw [← hqdeg]
      exact hqm.coeff_natDegree
    have hfc : (F a).coeff (heatRegularHead a j) = 1 := by
      rw [← (hFm a).2]
      exact (hFm a).1.coeff_natDegree
    simpa only [coeff_C_mul, hqc, hfc, mul_one] using hh
  have hc0 : (((heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr (show
      N - heatRegularHead a j ≤ heatRegularGap a j - 1 by omega))
  have hFq : F a = q := by
    rw [← hconstants] at heq
    exact (mul_left_cancel₀ (by simpa using hc0) heq).symm
  refine ⟨j, hj, hj1, b, F, S, hFm, hFa, hFq, hS, ?_, hPF, hscale, hSF⟩
  rw [hFq]
  exact hSa

/-- Every nearby admission root lies in the analytic finite factor or is one
of the known simple-pole branches. No additional escape packet is omitted. -/
theorem hcf_heat_admission_root_partition (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      ∃ (b : ∀ z : (heatEscapePolynomial (heatRegularGap a j)
          (N - heatRegularHead a j)).rootSet ℂ, HeatAdmissionEscapingBranch a N z)
        (F : ℝ → ℂ[X]),
        (∀ t, (F t).Monic ∧ (F t).natDegree = heatRegularHead a j) ∧
        (∀ i, AnalyticAt ℝ (fun t => (F t).coeff i) a) ∧
        F a = (monicMomentAdmissionPolynomial (heatRealMoments a)
          (heatRegularHead a j)).map (algebraMap ℝ ℂ) ∧
        ∀ᶠ t in 𝓝[≠] (a : ℝ), ∀ w : ℂ,
          aeval w (monicMomentAdmissionPolynomial (heatRealMoments t) N) = 0 ↔
            (F t).eval w = 0 ∨ ∃ z, w = (b z).scaledRoot t / ((t - a : ℝ) : ℂ) := by
  classical
  obtain ⟨j, hj, hj1, b, F, _, hFm, hFa, hF0, _, _, hPF, _, _⟩ :=
    hcf_heat_admission_finite_factor a N
  refine ⟨j, hj, hj1, b, F, hFm, hFa, hF0, ?_⟩
  filter_upwards [hPF] with t ht w
  rw [← eval_map_algebraMap, ht, eval_mul, mul_eq_zero]
  have hB : (escapingRootFactor (fun z => (b z).scaledRoot) a t).eval w = 0 ↔
      ∃ z, w = (b z).scaledRoot t / ((t - a : ℝ) : ℂ) := by
    simp [escapingRootFactor, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]
  rw [hB, or_comm]

end
end RHTower
