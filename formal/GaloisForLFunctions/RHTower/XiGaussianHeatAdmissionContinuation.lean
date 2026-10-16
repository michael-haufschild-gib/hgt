import GaloisForLFunctions.HTGeometry.HankelHeatAdmissionFlow
import GaloisForLFunctions.HTGeometry.MeromorphicPolePrimitive
import GaloisForLFunctions.RHTower.XiGaussianHeatTodaMultiplicity

/-!
# Canonical admission continues through every actual heat singularity

In a normal block with regular heads `n` and `n+d`, the degree `n+k`
monic admission has exact polynomial pole order `k`. Multiplication by
`(t-a)^k` gives an analytic coefficient vector whose value is
`(d-1).descFactorial k` times the regular-head admission. Thus all missing
degrees have the same canonical projective limit, even at simultaneous,
high-order determinant contacts.

The final all-time theorem assumes only positive time and rank. It resolves
the breakdown of monic admission coordinates; it does not assert source
positivity or exclude singular contacts.
-/

open Filter Topology Matrix HTGeometry

namespace RHTower
noncomputable section

/-- A coefficient of the actual canonical monic heat admission. -/
def heatAdmissionCoeff (N i : ℕ) (t : ℝ) : ℝ :=
  (monicMomentAdmissionPolynomial (heatRealMoments t) N).coeff i

theorem analyticAt_heatRealMoments {a : ℝ} (ha : 0 < a) (k : ℕ) :
    AnalyticAt ℝ (fun t => heatRealMoments t k) a := by
  simpa only [heatMomentArray, heatRealMoments, Nat.add_zero] using
    analyticAt_heatMomentArray ha k 0

theorem meromorphicAt_heatAdmissionCoeff {a : ℝ} (ha : 0 < a) (N i : ℕ) :
    MeromorphicAt (heatAdmissionCoeff N i) a :=
  meromorphicAt_monicMomentAdmissionPolynomial_coeff (analyticAt_heatRealMoments ha) N i

theorem analyticAt_heatAdmissionCoeff {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hN : heatMomentDet N a ≠ 0) (i : ℕ) :
    AnalyticAt ℝ (heatAdmissionCoeff N i) a :=
  analyticAt_monicMomentAdmissionPolynomial_coeff (analyticAt_heatRealMoments ha) hN i

/-- The connection holds as a punctured germ at every positive time,
including a time when either adjacent determinant vanishes. -/
theorem eventually_deriv_heatAdmissionCoeff (a : {t : ℝ // 0 < t}) (n i : ℕ) :
    deriv (heatAdmissionCoeff (n + 1) i) =ᶠ[𝓝[≠] (a : ℝ)]
      (fun t => deriv (logDeriv (heatMomentDet (n + 1))) t * heatAdmissionCoeff n i t) := by
  filter_upwards [eventually_heatMomentDet_ne_zero a.property n,
    eventually_heatMomentDet_ne_zero a.property (n + 1),
    (eventually_gt_nhds a.property).filter_mono nhdsWithin_le_nhds] with t hn hn1 ht
  have hlast :
      (fun u => monicMomentAdmissionCoefficients (heatRealMoments u) (n + 1) (Fin.last n))
        =ᶠ[𝓝 t] logDeriv (heatMomentDet (n + 1)) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact monicMomentAdmissionCoefficients_last_eq_logDeriv
      (fun k => hasDerivAt_heatRealMoments k hu) n
  have hv := deriv_monicMomentAdmissionCoefficients (analyticAt_heatRealMoments ht)
    (fun k => hasDerivAt_heatRealMoments k ht) hn hn1
  by_cases hi : i < n + 1
  · have h := congrFun hv ⟨i, hi⟩
    rw [hlast.deriv_eq] at h
    rw [show heatAdmissionCoeff (n + 1) i =
      fun u => monicMomentAdmissionCoefficients (heatRealMoments u) (n + 1) ⟨i, hi⟩ by
      funext u; exact monicMomentAdmissionPolynomial_coeff_lt _ hi]
    simpa only [heatAdmissionCoeff,
      Pi.smul_apply, smul_eq_mul, ← monicMomentAdmissionPolynomial_coeff_fin] using h
  · have hni : n < i := by omega
    rw [show heatAdmissionCoeff n i = fun _ => 0 by
      funext u; exact monicMomentAdmissionPolynomial_coeff_gt _ hni, mul_zero]
    rcases eq_or_lt_of_le (Nat.le_of_not_gt hi) with he | he
    · subst i
      rw [show heatAdmissionCoeff (n + 1) (n + 1) = fun _ => 1 by
        funext u; exact monicMomentAdmissionPolynomial_coeff_self _ _]
      exact deriv_const t 1
    · rw [show heatAdmissionCoeff (n + 1) i = fun _ => 0 by
        funext u; exact monicMomentAdmissionPolynomial_coeff_gt _ he]
      exact deriv_const t 0

/-- Exact analytic cancellation throughout one actual normal block. -/
theorem heat_normal_block_admission_continuation (a : {t : ℝ // 0 < t})
    {n d : ℕ} (hblock : MomentNormalBlock (heatRealMoments a) n d) :
    ∀ k < d, ∀ i : ℕ, ScaledAnalyticGerm (heatAdmissionCoeff (n + k) i) a k
      (((d - 1).descFactorial k : ℝ) * heatAdmissionCoeff n i a) := by
  intro k
  induction k with
  | zero =>
      intro _ i
      simpa only [Nat.add_zero, Nat.descFactorial_zero, Nat.cast_one, one_mul] using
        (analyticAt_heatAdmissionCoeff a.property hblock.head_regular i).scaledAnalyticGerm
  | succ k ih =>
      intro hk i
      have hprev := ih (by omega) i
      have horder : analyticOrderAt (heatMomentDet (n + (k + 1))) (a : ℝ) =
          (((k + 1) * (d - (k + 1)) : ℕ) : ℕ∞) := by
        rw [analyticOrderAt_heatMomentDet_eq,
          heat_normal_block_multiplicity a hblock (k + 1) (by omega)]
      have hcurv := scaledAnalyticGerm_logDeriv_deriv
        (analyticAt_heatMomentDet a.property (n + (k + 1))) horder
      have hprod := hcurv.mul hprev
      have hder : ScaledAnalyticGerm (deriv (heatAdmissionCoeff (n + (k + 1)) i)) a
          ((k + 1) + 1)
          (-(((k + 1) * (d - (k + 1)) : ℕ) : ℝ) *
            (((d - 1).descFactorial k : ℝ) * heatAdmissionCoeff n i a)) := by
        have he := eventually_deriv_heatAdmissionCoeff a (n + k) i
        rw [Nat.add_assoc] at he
        convert hprod.congr he.symm using 1
        omega
      have hprimitive := scaledAnalyticGerm_of_deriv
        (meromorphicAt_heatAdmissionCoeff a.property (n + (k + 1)) i)
        (Nat.succ_pos k) hder
      have hfactor :
          -(-(((k + 1) * (d - (k + 1)) : ℕ) : ℝ) *
            (((d - 1).descFactorial k : ℝ) * heatAdmissionCoeff n i a)) / (k + 1 : ℕ) =
          ((d - 1).descFactorial (k + 1) : ℝ) * heatAdmissionCoeff n i a := by
        rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul]
        have hidx : d - 1 - k = d - (k + 1) := by omega
        rw [hidx]
        have hkne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        field_simp
      simpa only [hfactor] using hprimitive

/-- Unconditional coefficientwise continuation at every positive heat time.
The explicit multiplier is nonzero because the offset lies inside its block. -/
theorem hcf_heat_admission_continuation (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      ∀ i : ℕ, ScaledAnalyticGerm (heatAdmissionCoeff N i) a (N - heatRegularHead a j)
        (((heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) : ℝ) *
          heatAdmissionCoeff (heatRegularHead a j) i a) := by
  obtain ⟨j, hj, hj1⟩ := exists_heatRegularHead_cover a N
  have hgap := heatRegularHead_add_gap a j
  have hk : N - heatRegularHead a j < heatRegularGap a j := by omega
  have he : heatRegularHead a j + (N - heatRegularHead a j) = N := by omega
  refine ⟨j, hj, hj1, ?_⟩
  simpa only [he] using heat_normal_block_admission_continuation a
    (heatRegularGap_normalBlock a j) (N - heatRegularHead a j) hk

/-- One specified coefficient certifies exact pole order of the entire
polynomial. The cancellation exponent cannot be decreased. -/
theorem hcf_heat_admission_exact_pole (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      meromorphicOrderAt (heatAdmissionCoeff N (heatRegularHead a j)) (a : ℝ) =
        ((-((N - heatRegularHead a j : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨j, hj, hj1, hc⟩ := hcf_heat_admission_continuation a N
  have hgap := heatRegularHead_add_gap a j
  have hpos : 0 < (heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) :=
    Nat.descFactorial_pos.mpr (by omega)
  have hne : ((heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)
  refine ⟨j, hj, hj1, (hc (heatRegularHead a j)).order_eq
    (meromorphicAt_heatAdmissionCoeff a.property _ _) ?_⟩
  simpa only [heatAdmissionCoeff, monicMomentAdmissionPolynomial_coeff_self, mul_one] using hne

/-- Canonical projective continuation through every singular heat time.
Normalizing by the coefficient at the preceding regular head gives an
analytic, nonzero vector, whose value is exactly that head's monic admission.
All coordinates agree on one punctured neighborhood. -/
theorem hcf_heat_admission_projective_extension (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ (j : ℕ) (g : ℝ → Fin (N + 1) → ℝ),
      heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      AnalyticAt ℝ g (a : ℝ) ∧
      g a = (fun i : Fin (N + 1) => heatAdmissionCoeff (heatRegularHead a j) i a) ∧
      g a ≠ 0 ∧
      (fun t (i : Fin (N + 1)) =>
        heatAdmissionCoeff N i t / heatAdmissionCoeff N (heatRegularHead a j) t)
        =ᶠ[𝓝[≠] (a : ℝ)] g := by
  classical
  obtain ⟨j, hj, hj1, hc⟩ := hcf_heat_admission_continuation a N
  have hgap := heatRegularHead_add_gap a j
  let C : ℝ := ((heatRegularGap a j - 1).descFactorial (N - heatRegularHead a j) : ℝ)
  have hC : C ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt
    (Nat.descFactorial_pos.mpr (show N - heatRegularHead a j ≤ heatRegularGap a j - 1 by omega)))
  have hcoords (i : Fin (N + 1)) : ∃ u : ℝ → ℝ, AnalyticAt ℝ u (a : ℝ) ∧
      u a = C * heatAdmissionCoeff (heatRegularHead a j) i a ∧
      (fun t => (t - a) ^ (N - heatRegularHead a j) * heatAdmissionCoeff N i t)
        =ᶠ[𝓝[≠] (a : ℝ)] u := hc i
  choose u hu hua hue using hcoords
  let r : Fin (N + 1) := ⟨heatRegularHead a j, by omega⟩
  have hr : u r a = C := by
    simpa only [r, heatAdmissionCoeff, monicMomentAdmissionPolynomial_coeff_self, mul_one]
      using hua r
  have hrne : u r a ≠ 0 := hr.trans_ne hC
  let g : ℝ → Fin (N + 1) → ℝ := fun t i => u i t / u r t
  have hg : AnalyticAt ℝ g (a : ℝ) :=
    analyticAt_pi_iff.mpr fun i => (hu i).div (hu r) hrne
  have hga : g a = fun i : Fin (N + 1) => heatAdmissionCoeff (heatRegularHead a j) i a := by
    funext i
    change u i a / u r a = _
    rw [hua i, hr]
    field_simp
  refine ⟨j, g, hj, hj1, hg, hga, ?_, ?_⟩
  · intro hz
    have hh := congrFun hz r
    rw [hga] at hh
    apply (one_ne_zero : (1 : ℝ) ≠ 0)
    simpa only [r, heatAdmissionCoeff, monicMomentAdmissionPolynomial_coeff_self,
      Pi.zero_apply] using hh
  · have heall : ∀ᶠ t in 𝓝[≠] (a : ℝ), ∀ i : Fin (N + 1),
        (t - a) ^ (N - heatRegularHead a j) * heatAdmissionCoeff N i t = u i t :=
      Filter.eventually_all.mpr hue
    filter_upwards [heall, self_mem_nhdsWithin] with t ht hta
    funext i
    change heatAdmissionCoeff N i t / heatAdmissionCoeff N (heatRegularHead a j) t =
      u i t / u r t
    rw [← ht i, ← ht r]
    have hp : (t - a) ^ (N - heatRegularHead a j) ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hta)
    exact (mul_div_mul_left _ _ hp).symm

end
end RHTower
