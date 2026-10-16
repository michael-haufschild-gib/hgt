import GaloisForLFunctions.HTGeometry.HankelHeatEscapePolynomial
import GaloisForLFunctions.HTGeometry.HeatEscapeNonreal
import GaloisForLFunctions.RHTower.XiGaussianHeatAdmissionContinuation

/-!
# The complete escaping polynomial at an actual heat singularity

The projective limit of a degree `n+k` admission remembers only the regular
head `P_n`. The weighted change of variable retains the missing degree:
`epsilon^(n+k) P_(n+k)(a+epsilon, X/epsilon)` extends coefficientwise
analytically to `X^n * heatEscapePolynomial d k`. Every coefficient of the
escaping packet is forced by the heat connection and the exact Toda orders.
-/

open Filter Topology Polynomial HTGeometry

namespace RHTower
noncomputable section

/-- All upper coefficients, at their individual exact blow-up scales. -/
theorem heat_normal_block_admission_upper_profile (a : {t : ℝ // 0 < t})
    {n d : ℕ} (hblock : MomentNormalBlock (heatRealMoments a) n d) :
    ∀ k < d, ∀ j ≤ k,
      ScaledAnalyticGerm (heatAdmissionCoeff (n + k) (n + j)) a (k - j)
        (heatEscapeCoeff d k j) := by
  intro k
  induction k with
  | zero =>
      intro _ j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa only [Nat.add_zero, Nat.sub_self, heatEscapeCoeff_self,
        heatAdmissionCoeff, monicMomentAdmissionPolynomial_coeff_self] using
        (analyticAt_heatAdmissionCoeff a.property hblock.head_regular n).scaledAnalyticGerm
  | succ k ih =>
      intro hk j hj
      by_cases hjtop : j = k + 1
      · subst j
        have he : heatAdmissionCoeff (n + (k + 1)) (n + (k + 1)) = fun _ => 1 := by
          funext t
          exact monicMomentAdmissionPolynomial_coeff_self _ _
        rw [Nat.sub_self, heatEscapeCoeff_self, he]
        exact analyticAt_const.scaledAnalyticGerm
      · have hjk : j ≤ k := by omega
        have hprev := ih (by omega) j hjk
        have horder : analyticOrderAt (heatMomentDet (n + (k + 1))) (a : ℝ) =
            (((k + 1) * (d - (k + 1)) : ℕ) : ℕ∞) := by
          rw [analyticOrderAt_heatMomentDet_eq,
            heat_normal_block_multiplicity a hblock (k + 1) (by omega)]
        have hcurv := scaledAnalyticGerm_logDeriv_deriv
          (analyticAt_heatMomentDet a.property (n + (k + 1))) horder
        have hprod := hcurv.mul hprev
        have hder : ScaledAnalyticGerm (deriv (heatAdmissionCoeff (n + (k + 1)) (n + j))) a
            ((k + 1 - j) + 1)
            (-(((k + 1) * (d - (k + 1)) : ℕ) : ℝ) * heatEscapeCoeff d k j) := by
          have he := eventually_deriv_heatAdmissionCoeff a (n + k) (n + j)
          rw [Nat.add_assoc] at he
          convert hprod.congr he.symm using 1
          omega
        have hprimitive := scaledAnalyticGerm_of_deriv
          (meromorphicAt_heatAdmissionCoeff a.property (n + (k + 1)) (n + j))
          (show 0 < k + 1 - j by omega) hder
        have hden : ((k + 1 - j : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (show k + 1 - j ≠ 0 by omega)
        have hvalue :
            -(-(((k + 1) * (d - (k + 1)) : ℕ) : ℝ) * heatEscapeCoeff d k j) /
              ((k + 1 - j : ℕ) : ℝ) = heatEscapeCoeff d (k + 1) j := by
          apply (div_eq_iff hden).mpr
          have hrec := heatEscapeCoeff_step (d := d) hjk
          nlinarith only [hrec]
        simpa only [hvalue] using hprimitive

/-- The complete weighted coefficient profile, including coefficients below
the preceding regular head. -/
theorem heat_normal_block_admission_escape_profile (a : {t : ℝ // 0 < t})
    {n d k : ℕ} (hblock : MomentNormalBlock (heatRealMoments a) n d) (hk : k < d)
    (i : Fin (n + k + 1)) :
    ScaledAnalyticGerm (heatAdmissionCoeff (n + k) i) a (n + k - i)
      ((X ^ n * heatEscapePolynomial d k).coeff i) := by
  by_cases hi : n ≤ i.val
  · have hj : i.val - n ≤ k := by omega
    have he : n + (i.val - n) = i.val := by omega
    have hscale : k - (i.val - n) = n + k - i.val := by omega
    have h := heat_normal_block_admission_upper_profile a hblock k hk (i.val - n) hj
    rw [he, hscale] at h
    rwa [coeff_X_pow_mul', if_pos hi, heatEscapePolynomial_coeff hj]
  · have hil : i.val < n := by omega
    have h := (heat_normal_block_admission_continuation a hblock k hk i).raise
      (show k < n + k - i.val by omega)
    rwa [coeff_X_pow_mul', if_neg hi]

/-- Unconditional resolution of the full polynomial at infinity. At every
positive time and rank the weighted coefficient vector has an analytic
extension with an explicit, universal, monic polynomial as its value. -/
theorem hcf_heat_admission_escape_profile (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ (j : ℕ) (g : ℝ → Fin (N + 1) → ℝ),
      heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      AnalyticAt ℝ g (a : ℝ) ∧
      g a = (fun i : Fin (N + 1) =>
        (X ^ heatRegularHead a j *
          heatEscapePolynomial (heatRegularGap a j) (N - heatRegularHead a j)).coeff i) ∧
      (fun t (i : Fin (N + 1)) => (t - a) ^ (N - i.val) * heatAdmissionCoeff N i t)
        =ᶠ[𝓝[≠] (a : ℝ)] g := by
  classical
  obtain ⟨j, hj, hj1⟩ := exists_heatRegularHead_cover a N
  have hgap := heatRegularHead_add_gap a j
  have hk : N - heatRegularHead a j < heatRegularGap a j := by omega
  have he : heatRegularHead a j + (N - heatRegularHead a j) = N := by omega
  have hc (i : Fin (N + 1)) : ScaledAnalyticGerm (heatAdmissionCoeff N i) a (N - i.val)
      ((X ^ heatRegularHead a j *
        heatEscapePolynomial (heatRegularGap a j) (N - heatRegularHead a j)).coeff i) := by
    have h := heat_normal_block_admission_escape_profile a (heatRegularGap_normalBlock a j)
      hk (⟨i.val, by omega⟩ : Fin (heatRegularHead a j + (N - heatRegularHead a j) + 1))
    simpa only [he] using h
  choose u hu hua hue using hc
  refine ⟨j, fun t i => u i t, hj, hj1, analyticAt_pi_iff.mpr hu, funext hua, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hue] with t ht
  exact funext ht

/-- An offset of at least two forces nonreal admission roots on both sides
of the contact. This uses the whole escaping polynomial, not just its degree. -/
theorem heat_normal_block_eventually_not_splits (a : {t : ℝ // 0 < t})
    {n d k : ℕ} (hblock : MomentNormalBlock (heatRealMoments a) n d)
    (hk : k < d) (hk2 : 2 ≤ k) :
    ∀ᶠ t in 𝓝[≠] (a : ℝ), ¬ (monicMomentAdmissionPolynomial (heatRealMoments t) (n + k)).Splits := by
  let p : ℝ → ℝ[X] := fun t => monicMomentAdmissionPolynomial (heatRealMoments t) (n + k)
  let q : ℝ[X] := X ^ n * heatEscapePolynomial d k
  have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (heatEscapePolynomial_ne_zero d k)
  have hqdeg : q.natDegree ≤ n + k := by
    simp only [q, natDegree_X_pow_mul n (heatEscapePolynomial_ne_zero d k),
      heatEscapePolynomial_natDegree]
    omega
  have hqns : ¬ q.Splits := by
    intro hs
    have hq := (splits_mul (pow_ne_zero n X_ne_zero) (heatEscapePolynomial_ne_zero d k)).mp hs
    exact heatEscapePolynomial_not_splits hk hk2 hq.2
  have hlim (i : ℕ) : Tendsto
      (fun t => (weightedPolynomial (p t) (n + k) (t - a)).coeff i)
      (𝓝[≠] (a : ℝ)) (𝓝 (q.coeff i)) := by
    by_cases hi : i ≤ n + k
    · have h := (heat_normal_block_admission_escape_profile a hblock hk
        (⟨i, by omega⟩ : Fin (n + k + 1))).tendsto
      simpa only [weightedPolynomial, ofFn_coeff_eq_val_of_lt _ (show i < n + k + 1 by omega),
        p, q, heatAdmissionCoeff] using h
    · have hi' : n + k < i := by omega
      simp only [weightedPolynomial, ofFn_coeff_eq_zero_of_ge _ (show n + k + 1 ≤ i by omega),
        coeff_eq_zero_of_natDegree_lt (hqdeg.trans_lt hi')]
      exact tendsto_const_nhds
  have hn := eventually_not_splits_of_coeff_limit
    (p := fun t => weightedPolynomial (p t) (n + k) (t - a))
    (fun _ => Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)) hqdeg hq0 hlim hqns
  filter_upwards [hn, self_mem_nhdsWithin] with t ht hta
  intro hs
  exact ht (weightedPolynomial_splits
    (le_of_eq (monicMomentAdmissionPolynomial_natDegree _ _)) (sub_ne_zero.mpr hta) hs)

/-- Unconditional actual-source dichotomy: at every positive time and rank,
the offset from the regular head is at most one, or the admissions throughout
a punctured neighborhood have a nonreal complex root. No source-sign,
regular-time, transversality, or real-rootedness premise is used. -/
theorem hcf_heat_admission_nonreal_escape (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      (N - heatRegularHead a j ≤ 1 ∨
        ∀ᶠ t in 𝓝[≠] (a : ℝ), ∃ z : ℂ, z.im ≠ 0 ∧
          (aeval z (monicMomentAdmissionPolynomial (heatRealMoments t) N) : ℂ) = 0) := by
  obtain ⟨j, hj, hj1⟩ := exists_heatRegularHead_cover a N
  refine ⟨j, hj, hj1, ?_⟩
  by_cases hk1 : N - heatRegularHead a j ≤ 1
  · exact Or.inl hk1
  · right
    have hgap := heatRegularHead_add_gap a j
    have hk : N - heatRegularHead a j < heatRegularGap a j := by omega
    have he : heatRegularHead a j + (N - heatRegularHead a j) = N := by omega
    have hn := heat_normal_block_eventually_not_splits a (heatRegularGap_normalBlock a j)
      hk (by omega)
    rw [he] at hn
    filter_upwards [hn] with t ht
    by_contra h
    push Not at h
    apply ht
    apply GaloisForLFunctions.HTGeometry.splits_of_forall_complex_root_real N _
      (le_of_eq (monicMomentAdmissionPolynomial_natDegree _ _))
    intro z hz
    by_contra him
    exact h z him hz

end
end RHTower
