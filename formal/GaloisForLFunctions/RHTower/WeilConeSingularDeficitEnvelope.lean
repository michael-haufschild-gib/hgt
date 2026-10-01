import GaloisForLFunctions.RHTower.WeilFullConeHerglotzCriticalHalfPlane
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.CosineSeriesBohrEnvelope
import GaloisForLFunctions.RHTower.EisensteinLineHeightOneMean
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# The singular deficit law of the Weil cone (envelope form)

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam`, and put `w = lam − Λ`.  For
a divisor copy `q` of `ξ` at `ρ = β + iγ` (multiplicity `m_ρ`) and `σ > 1` put
`A_q(t) = (σ − β)/((σ − β)² + (t − γ)²)`, the Poisson term of `Re ξ'/ξ(σ + it)`.  Give each copy
the **deficit weight**

* `d_q = (1 − μ_lam({γ})/m_ρ)⁺` if `ρ` is on the critical line,
* `d_q = 1` otherwise,

and let `ε_σ(t) = Σ_q d_q A_q(t)`: the Poisson-smoothed count of off-line zeros together with the
critical zero mass that `μ_lam` fails to carry.

**Theorem** (`abs_sub_vonMangoldt_le_of_envelope`).  If the mean of `ε_σ` over `[8, T]` is at most
`E + η` along arbitrarily large `T`, for every `η > 0`, then `|w(m)| m^{−σ} ≤ 4E` for every `m ≥ 2`.

**Proof.**  On `Re s > 1`, `Re Φ_lam − Re ξ'/ξ = −Σ w(n)n^{−σ}cos(t log n)` (Dirichlet series).
The boundary measure gives `Re Φ_lam(σ + it) ≥ Σ_{critical} μ_lam({γ}) A_ρ(t)`, and Hadamard gives
`Re ξ'/ξ = Σ_q A_q`.  Hence the cosine series is `≥ −ε_σ`, and the Bohr envelope bound
(`CosineSeriesBohrEnvelope`) applies.

This is the formal envelope step of the singular deficit law (HF L126); the counting of `ε_σ` by
zeros is the remaining bookkeeping.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ## The zero side -/

/-- The Poisson term of a divisor copy at `σ + it`. -/
def copyPoisson (σ t : ℝ) (q : XiZeroCopy) : ℝ :=
  (σ - (q.1 : ℂ).re) / ((σ - (q.1 : ℂ).re) ^ 2 + (t - (q.1 : ℂ).im) ^ 2)

theorem normSq_sub_copy (σ t : ℝ) (z : ℂ) :
    normSq ((σ : ℂ) + t * I - z) = (σ - z.re) ^ 2 + (t - z.im) ^ 2 := by
  rw [normSq_apply]
  simp
  ring

theorem copyPoisson_pos {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) (q : XiZeroCopy) : 0 < copyPoisson σ t q := by
  obtain ⟨_, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
  unfold copyPoisson
  have h : 0 < σ - (q.1 : ℂ).re := by linarith
  positivity

theorem reflect_copy_coe (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl

theorem paired_eq_copyPoisson (σ t : ℝ) (q : XiZeroCopy) :
    xiPairedResolventTerm ((σ : ℂ) + t * I) q =
      copyPoisson σ t q + copyPoisson σ t (xiZeroCopyReflectEquiv q) := by
  unfold xiPairedResolventTerm copyPoisson
  rw [reflect_copy_coe, normSq_sub_copy, show ((σ : ℂ) + t * I - (1 - (q.1 : ℂ))) =
    (σ : ℂ) + t * I - ((1 : ℂ) - (q.1 : ℂ)) from rfl, normSq_sub_copy]
  simp

theorem summable_copyPoisson {σ : ℝ} (hσ : 1 < σ) (t : ℝ) : Summable (copyPoisson σ t) := by
  have hxi : xi ((σ : ℂ) + t * I) ≠ 0 := xi_ne_zero_of_one_lt_re (by simpa using hσ)
  refine (summable_xiPairedResolventTerm hxi).of_nonneg_of_le
    (fun q => (copyPoisson_pos hσ.le t q).le) fun q => ?_
  rw [paired_eq_copyPoisson]
  linarith [copyPoisson_pos hσ.le t (xiZeroCopyReflectEquiv q)]

/-- **Hadamard on `Re s > 1`.** `Re ξ'/ξ(σ + it) = Σ_q A_q(t)`. -/
theorem re_logDeriv_xi_eq_tsum_copyPoisson {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (logDeriv xi ((σ : ℂ) + t * I)).re = ∑' q, copyPoisson σ t q := by
  have hxi : xi ((σ : ℂ) + t * I) ≠ 0 := xi_ne_zero_of_one_lt_re (by simpa using hσ)
  have h2 := two_mul_re_logDeriv_xi_eq_tsum_paired hxi
  have hs := summable_copyPoisson hσ t
  have hsR : Summable fun q => copyPoisson σ t (xiZeroCopyReflectEquiv q) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr hs
  simp_rw [paired_eq_copyPoisson] at h2
  rw [hs.tsum_add hsR, Equiv.tsum_eq xiZeroCopyReflectEquiv (copyPoisson σ t)] at h2
  linarith

/-! ## The Dirichlet side -/

/-- The cosine coefficients `(Λ(n) − lam(n)) n^{−σ}` on `n ≥ 2`. -/
def deviationCoeff (lam : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) * (n : ℝ) ^ (-σ) else 0

theorem logDeriv_xi_eq_datum {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [logDeriv_xi_eq_of_ne hs0 hs1 (xi_ne_zero_of_one_lt_re hs), logDeriv_completedRiemannZeta_eq hs,
    logDeriv_Gammaℝ_of_re_pos (by linarith), logDeriv_apply,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, zetaArchimedeanDatum]
  ring

theorem summable_abs_deviationCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n => |deviationCoeff lam σ n| := by
  have h1 := WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  have h2 : Summable fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ σ := by
    have := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
    refine (LSeriesSummable_iff_of_re_eq_re (s' := (σ : ℂ)) rfl).mp this |>.norm |>.congr ?_
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · subst h; simp
    · simp
  refine ((h1.add h2)).of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_
  unfold deviationCoeff
  split_ifs with hn
  · have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _), Real.rpow_neg hpos.le, ← div_eq_mul_inv]
    have := abs_sub (ArithmeticFunction.vonMangoldt n : ℝ) (lam n)
    have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hpos _
    rw [← add_div, div_le_div_iff_of_pos_right hp]
    linarith
  · simp only [abs_zero]
    positivity

/-- On `Re s > 1`, `Re Φ_lam − Re ξ'/ξ` is the cosine series of the deviation. -/
theorem re_weilFunction_sub_re_logDeriv_xi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    (weilFunction lam ((σ : ℂ) + t * I)).re - (logDeriv xi ((σ : ℂ) + t * I)).re =
      logCosSeries (deviationCoeff lam σ) t := by
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hs : 1 < s.re := by simpa [hsdef] using hσ
  rw [logDeriv_xi_eq_datum hs, weilFunction]
  have hL1 := summable_term_lamC hW hs
  have hL2 : Summable fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hdiff : (zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamC lam) s) -
      (zetaArchimedeanDatum s + 1 / (s - 1) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) =
      ∑' n, (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n -
        LSeries.term (lamC lam) s n) := by
    rw [LSeries, LSeries, hL2.tsum_sub hL1]
    ring
  rw [show digamma (s / 2) / 2 - (Real.log π : ℂ) / 2 + 1 / s + 1 / (s - 1) - LSeries (lamC lam) s
      = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamC lam) s by rw [zetaArchimedeanDatum],
    ← Complex.sub_re, hdiff, Complex.re_tsum (hL2.sub hL1), logCosSeries]
  refine tsum_congr fun n => ?_
  rw [Complex.sub_re, LSeries.term_def, LSeries.term_def]
  unfold deviationCoeff lamC
  by_cases hn : 2 ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [if_neg hn0, if_neg hn0, if_pos hn, if_pos hn]
    have hcpow : ((n : ℂ) ^ s)⁻¹ = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        cexp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
      have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log hpos.le]
      rw [← Complex.cpow_neg, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0), hlog,
        Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      rw [hsdef]
      push_cast
      ring
    rw [div_eq_mul_inv, div_eq_mul_inv, hcpow]
    have hre : ∀ c : ℝ, (((c : ℝ) : ℂ) * ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        cexp (-(((t * Real.log n : ℝ) : ℂ) * I)))).re =
        c * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
      intro c
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
        show -(((t * Real.log n : ℝ) : ℂ) * I) = ((-(t * Real.log n) : ℝ) : ℂ) * I by
          push_cast; ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    rw [show ((ArithmeticFunction.vonMangoldt n : ℂ)) = (((ArithmeticFunction.vonMangoldt n : ℝ)) : ℂ)
      from rfl, hre, hre]
    ring
  · rw [if_neg hn]
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : n = 0 := by omega
      subst this
      simp
    · have : n = 1 := by omega
      subst this
      simp

/-! ## The Weil side: atoms of the boundary measure -/

/-- The multiplicity of a divisor point of `ξ`. -/
def xiDivisorMult (ρ : XiDivisorSupport) : ℕ := Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))

theorem xiDivisorMult_pos (ρ : XiDivisorSupport) : 0 < xiDivisorMult ρ := by
  have hpos := xi_divisor_pos_on_support ρ
  unfold xiDivisorMult
  omega

/-- The share of the atom of `μ_lam` at the ordinate of a critical copy. -/
def atomShare {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) : ℝ :=
  ((boundaryMeasure hW) {(q.1 : ℂ).im}).toReal / xiDivisorMult q.1

/-- The weight carried by `μ_lam` at a copy: its atom share if critical, `0` otherwise. -/
def carriedWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re = 1 / 2 then atomShare hW q else 0

/-- The deficit weight: `(1 − share)⁺` at critical copies, `1` off the line. -/
def deficitWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re = 1 / 2 then max (1 - atomShare hW q) 0 else 1

theorem deficitWeight_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) :
    0 ≤ deficitWeight hW q := by
  unfold deficitWeight
  split_ifs
  · exact le_max_right _ _
  · norm_num

theorem deficitWeight_le_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) :
    deficitWeight hW q ≤ 1 := by
  unfold deficitWeight
  have h0 : 0 ≤ atomShare hW q := div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  split_ifs
  · exact max_le (by linarith) zero_le_one
  · exact le_rfl

theorem carriedWeight_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) :
    0 ≤ carriedWeight hW q := by
  unfold carriedWeight atomShare
  split_ifs
  · exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  · exact le_rfl

theorem one_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (q : XiZeroCopy) :
    1 - carriedWeight hW q ≤ deficitWeight hW q := by
  unfold carriedWeight deficitWeight
  split_ifs
  · exact le_max_left _ _
  · norm_num

/-! ## The atomic lower bound -/

/-- The critical divisor points. -/
def CritPoint : Type := {ρ : XiDivisorSupport // ((ρ : ℂ)).re = 1 / 2}

instance : Countable CritPoint := by unfold CritPoint; infer_instance

theorem critOrd_injective : Function.Injective (fun ρ : CritPoint => ((ρ.1 : ℂ)).im) := by
  intro a b h
  have hab : ((a.1 : ℂ)) = ((b.1 : ℂ)) := Complex.ext (by rw [a.2, b.2]) h
  exact Subtype.ext (Subtype.ext hab)

theorem poissonDensity_toReal (w : ℂ) (r : ℝ) :
    (poissonDensity w r).toReal = 1 / (w.re ^ 2 + (r - w.im) ^ 2) := by
  unfold poissonDensity
  rw [ENNReal.coe_toReal, NNReal.coe_pow, coe_nnnorm, norm_div, norm_one, div_pow, one_pow,
    Complex.sq_norm, normSq_sub_I_mul]

theorem poissonDensity_ne_top (w : ℂ) (r : ℝ) : poissonDensity w r ≠ ⊤ := ENNReal.coe_ne_top

/-- The atoms of `μ_lam` at critical ordinates are bounded by its Poisson integral. -/
theorem tsum_crit_atoms_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (w : ℂ) :
    ∑' ρ : CritPoint, (boundaryMeasure hW) {((ρ.1 : ℂ)).im} * poissonDensity w ((ρ.1 : ℂ)).im ≤
      ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW := by
  set μ := boundaryMeasure hW
  set S : Set ℝ := Set.range fun ρ : CritPoint => ((ρ.1 : ℂ)).im with hS
  have hSc : S.Countable := Set.countable_range _
  have heq : (∑' ρ : CritPoint, μ {((ρ.1 : ℂ)).im} * poissonDensity w ((ρ.1 : ℂ)).im) =
      ∑' γ : S, poissonDensity w γ * μ {(γ : ℝ)} := by
    rw [← Equiv.tsum_eq (Equiv.ofInjective _ critOrd_injective)]
    refine tsum_congr fun ρ => ?_
    simp [Equiv.ofInjective, mul_comm]
  rw [heq, ← lintegral_countable _ hSc]
  exact setLIntegral_le_lintegral _ _

/-- **The atomic lower bound.**  `Σ_{critical copies} (μ_lam({γ})/m_ρ) A_q ≤ Re Φ_lam(σ + it)`. -/
theorem tsum_carried_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun q => carriedWeight hW q * copyPoisson σ t q) ∧
      ∑' q, carriedWeight hW q * copyPoisson σ t q ≤ (weilFunction lam ((σ : ℂ) + t * I)).re := by
  set μ := boundaryMeasure hW with hμ
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hs : 1 < s.re := by simpa [hsdef] using hσ
  set w : ℂ := s - 1 / 2 with hwdef
  have hwre : w.re = σ - 1 / 2 := by simp [hwdef, hsdef]
  have hwim : w.im = t := by simp [hwdef, hsdef]
  have hb : 0 < σ - 1 / 2 := by linarith
  have hfnn : ∀ q, 0 ≤ carriedWeight hW q * copyPoisson σ t q := fun q =>
    mul_nonneg (carriedWeight_nonneg hW q) (copyPoisson_pos hσ.le t q).le
  set F : XiZeroCopy → ℝ≥0∞ := fun q => ENNReal.ofReal (carriedWeight hW q * copyPoisson σ t q)
    with hF
  -- the critical Poisson term is `b` times the Poisson density
  have hcrit : ∀ q : XiZeroCopy, ((q.1 : ℂ)).re = 1 / 2 →
      copyPoisson σ t q = (σ - 1 / 2) * (poissonDensity w ((q.1 : ℂ)).im).toReal := by
    intro q hq
    rw [poissonDensity_toReal, hwre, hwim, copyPoisson, hq]
    have hd : (σ - 1 / 2) ^ 2 + (((q.1 : ℂ)).im - t) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  -- fibrewise bound
  have hfib : ∀ ρ : XiDivisorSupport, (∑' i : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ)
      (ρ : ℂ))), F ⟨ρ, i⟩) ≤
      if ((ρ : ℂ)).re = 1 / 2 then
        ENNReal.ofReal (σ - 1 / 2) * (μ {((ρ : ℂ)).im} * poissonDensity w ((ρ : ℂ)).im)
      else 0 := by
    intro ρ
    have hconst : ∀ i : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
        F ⟨ρ, i⟩ = F ⟨ρ, ⟨0, xiDivisorMult_pos ρ⟩⟩ := fun i => rfl
    rw [tsum_fintype]
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hm : (0 : ℝ) < xiDivisorMult ρ := by exact_mod_cast xiDivisorMult_pos ρ
    split_ifs with hc
    · have hq : F ⟨ρ, ⟨0, xiDivisorMult_pos ρ⟩⟩ = ENNReal.ofReal ((μ {((ρ : ℂ)).im}).toReal / xiDivisorMult ρ *
          ((σ - 1 / 2) * (poissonDensity w ((ρ : ℂ)).im).toReal)) := by
        simp only [hF, carriedWeight, atomShare]
        rw [if_pos hc, hcrit ⟨ρ, ⟨0, xiDivisorMult_pos ρ⟩⟩ hc]
      rw [hq, nsmul_eq_mul]
      change ((xiDivisorMult ρ : ℕ) : ℝ≥0∞) * _ ≤ _
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      have halg : (xiDivisorMult ρ : ℝ) * ((μ {((ρ : ℂ)).im}).toReal / xiDivisorMult ρ *
          ((σ - 1 / 2) * (poissonDensity w ((ρ : ℂ)).im).toReal)) =
          (σ - 1 / 2) * ((μ {((ρ : ℂ)).im}).toReal * (poissonDensity w ((ρ : ℂ)).im).toReal) := by
        field_simp
      rw [halg, ENNReal.ofReal_mul hb.le]
      gcongr
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (poissonDensity_ne_top w _)]
      gcongr
      exact ENNReal.ofReal_toReal_le
    · have hz : F ⟨ρ, ⟨0, xiDivisorMult_pos ρ⟩⟩ = 0 := by
        simp only [hF, carriedWeight]
        rw [if_neg hc, zero_mul, ENNReal.ofReal_zero]
      simp [hz]
  -- assemble
  have hkey : (∑' q, F q) ≤ ENNReal.ofReal (σ - 1 / 2) * ∫⁻ r, poissonDensity w r ∂μ := by
    rw [ENNReal.tsum_sigma']
    refine (ENNReal.tsum_le_tsum hfib).trans ?_
    have hsub : (∑' ρ : XiDivisorSupport, if ((ρ : ℂ)).re = 1 / 2 then
        ENNReal.ofReal (σ - 1 / 2) * (μ {((ρ : ℂ)).im} * poissonDensity w ((ρ : ℂ)).im) else 0) =
        ENNReal.ofReal (σ - 1 / 2) *
          ∑' ρ : CritPoint, μ {((ρ.1 : ℂ)).im} * poissonDensity w ((ρ.1 : ℂ)).im := by
      rw [← ENNReal.tsum_mul_left]
      set g : XiDivisorSupport → ℝ≥0∞ := fun ρ => ENNReal.ofReal (σ - 1 / 2) *
        (μ {((ρ : ℂ)).im} * poissonDensity w ((ρ : ℂ)).im) with hg
      have := tsum_subtype {ρ : XiDivisorSupport | ((ρ : ℂ)).re = 1 / 2} g
      calc (∑' ρ : XiDivisorSupport, if ((ρ : ℂ)).re = 1 / 2 then g ρ else 0)
          = ∑' ρ, ({ρ : XiDivisorSupport | ((ρ : ℂ)).re = 1 / 2}).indicator g ρ := by
            refine tsum_congr fun ρ => ?_
            simp only [Set.indicator, Set.mem_setOf_eq]
            split_ifs <;> rfl
        _ = ∑' x : ({ρ : XiDivisorSupport | ((ρ : ℂ)).re = 1 / 2} : Set XiDivisorSupport),
              g x := this.symm
        _ = _ := rfl
    rw [hsub]
    gcongr
    exact tsum_crit_atoms_le hW w
  have hfin : (∫⁻ r, poissonDensity w r ∂μ) ≠ ⊤ := by
    rw [hwdef, hsdef, lintegral_poissonDensity_eq hW hs]
    exact ENNReal.ofReal_ne_top
  have hFfin : (∑' q, F q) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hkey
  have hsum : Summable fun q => carriedWeight hW q * copyPoisson σ t q := by
    refine (ENNReal.summable_toReal hFfin).congr fun q => ?_
    exact ENNReal.toReal_ofReal (hfnn q)
  refine ⟨hsum, ?_⟩
  have hval : (∑' q, carriedWeight hW q * copyPoisson σ t q) = (∑' q, F q).toReal := by
    rw [ENNReal.tsum_toReal_eq fun q => ENNReal.ofReal_ne_top]
    refine tsum_congr fun q => ?_
    exact (ENNReal.toReal_ofReal (hfnn q)).symm
  rw [hval]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hkey).trans
    (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.le, ← hwre, ← re_herglotzFunction hW
    (by rw [hwre]; exact hb), hwdef, re_herglotzFunction_eq hW hs]

/-! ## Continuity of weighted Poisson sums -/

theorem summable_inv_one_add_sq_im : Summable fun q : XiZeroCopy => 1 / (1 + ((q.1 : ℂ)).im ^ 2) := by
  refine ((summable_copyPoisson (σ := 2) (by norm_num) 0).mul_left 4).of_nonneg_of_le
    (fun q => by positivity) fun q => ?_
  obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
  unfold copyPoisson
  set β := ((q.1 : ℂ)).re
  set γ := ((q.1 : ℂ)).im
  have h1 : 1 < 2 - β := by linarith
  have h2 : 2 - β < 2 := by linarith
  rw [show (0 : ℝ) - γ = -γ by ring, neg_sq]
  rw [div_le_iff₀ (by positivity)]
  have hden : 0 < (2 - β) ^ 2 + γ ^ 2 := by nlinarith [sq_nonneg γ]
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [sq_nonneg γ]

theorem copyPoisson_le_local {σ : ℝ} (hσ : 1 < σ) {R t : ℝ} (ht : |t| ≤ R) (q : XiZeroCopy) :
    copyPoisson σ t q ≤ ((1 + (2 * R + 2) ^ 2) / (σ - 1) + 8 * σ) *
      (1 / (1 + ((q.1 : ℂ)).im ^ 2)) := by
  obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
  unfold copyPoisson
  set β := ((q.1 : ℂ)).re
  set γ := ((q.1 : ℂ)).im
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have hx : 0 < σ - β := by linarith
  have hx1 : σ - 1 < σ - β := by linarith
  have hσ1 : 0 < σ - 1 := by linarith
  have hq : 0 < 1 + γ ^ 2 := by positivity
  have hK1 : 0 ≤ (1 + (2 * R + 2) ^ 2) / (σ - 1) * (1 / (1 + γ ^ 2)) := by positivity
  have hK2 : 0 ≤ 8 * σ * (1 / (1 + γ ^ 2)) := by positivity
  rw [add_mul]
  rcases le_or_gt |γ| (2 * R + 2) with hγ | hγ
  · have hγ2 : γ ^ 2 ≤ (2 * R + 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg γ) hγ 2
    have h1 : (σ - β) / ((σ - β) ^ 2 + (t - γ) ^ 2) ≤ 1 / (σ - β) := by
      rw [div_le_div_iff₀ (by positivity) hx]
      nlinarith [sq_nonneg (t - γ)]
    have h2 : 1 / (σ - β) ≤ 1 / (σ - 1) := one_div_le_one_div_of_le hσ1 hx1.le
    have h3 : 1 / (σ - 1) ≤ (1 + (2 * R + 2) ^ 2) / (σ - 1) * (1 / (1 + γ ^ 2)) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hσ1 (by positivity)]
      nlinarith
    linarith
  · have htγ : |γ| / 2 ≤ |t - γ| := by
      have := abs_sub_abs_le_abs_sub γ t
      rw [abs_sub_comm] at this
      linarith
    have hsq : γ ^ 2 / 4 ≤ (t - γ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) htγ 2
      rw [div_pow, sq_abs, sq_abs] at this
      linarith
    have hγ1 : 1 ≤ γ ^ 2 := by
      have : (1 : ℝ) ≤ |γ| := by linarith
      have := pow_le_pow_left₀ zero_le_one this 2
      rw [sq_abs, one_pow] at this
      exact this
    have hy : 0 < (t - γ) ^ 2 := by linarith
    have h1 : (σ - β) / ((σ - β) ^ 2 + (t - γ) ^ 2) ≤ σ / (γ ^ 2 / 4) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (σ - β)]
    have h2 : σ / (γ ^ 2 / 4) ≤ 8 * σ * (1 / (1 + γ ^ 2)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hq]
      nlinarith
    linarith

/-- Weighted Poisson sums with weights in `[0, 1]` are continuous in `t`. -/
theorem continuous_weighted_copyPoisson {σ : ℝ} (hσ : 1 < σ) {c : XiZeroCopy → ℝ}
    (hc0 : ∀ q, 0 ≤ c q) (hc1 : ∀ q, c q ≤ 1) :
    Continuous fun t => ∑' q, c q * copyPoisson σ t q := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set R : ℝ := |t₀| + 1
  have hon : ContinuousOn (fun t => ∑' q, c q * copyPoisson σ t q) (Set.Icc (-R) R) := by
    refine continuousOn_tsum (f := fun q t => c q * copyPoisson σ t q)
      (u := fun q => ((1 + (2 * R + 2) ^ 2) / (σ - 1) + 8 * σ) *
      (1 / (1 + ((q.1 : ℂ)).im ^ 2))) (fun q => ?_) (summable_inv_one_add_sq_im.mul_left _)
      (fun q t ht => ?_)
    · refine (continuous_const.mul ?_).continuousOn
      unfold copyPoisson
      obtain ⟨_, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
      refine continuous_const.div (by fun_prop) fun t => ?_
      have : 0 < σ - ((q.1 : ℂ)).re := by linarith
      positivity
    · have htR : |t| ≤ R := abs_le.mpr ⟨ht.1, ht.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc0 q) (copyPoisson_pos hσ.le t q).le)]
      calc c q * copyPoisson σ t q ≤ 1 * copyPoisson σ t q :=
            mul_le_mul_of_nonneg_right (hc1 q) (copyPoisson_pos hσ.le t q).le
        _ ≤ _ := by rw [one_mul]; exact copyPoisson_le_local hσ htR q
  have hmem : Set.Icc (-R) R ∈ 𝓝 t₀ := by
    refine Icc_mem_nhds ?_ ?_
    · have := neg_abs_le t₀; linarith
    · have := le_abs_self t₀; linarith
  exact hon.continuousAt hmem

/-! ## The envelope -/

/-- The deficit envelope `ε_σ(t) = Σ_q d_q A_q(t)`. -/
def deficitEnvelope {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (σ t : ℝ) : ℝ :=
  ∑' q, deficitWeight hW q * copyPoisson σ t q

theorem deficitEnvelope_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) : 0 ≤ deficitEnvelope hW σ t :=
  tsum_nonneg fun q => mul_nonneg (deficitWeight_nonneg hW q) (copyPoisson_pos hσ.le t q).le

theorem continuous_deficitEnvelope {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ}
    (hσ : 1 < σ) : Continuous (deficitEnvelope hW σ) :=
  continuous_weighted_copyPoisson hσ (deficitWeight_nonneg hW) (deficitWeight_le_one hW)

/-- **The lower envelope.**  `Σ_n (Λ − lam)(n) n^{−σ} cos(t log n) ≥ −ε_σ(t)`. -/
theorem neg_deficitEnvelope_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) : -deficitEnvelope hW σ t ≤ logCosSeries (deviationCoeff lam σ) t := by
  rw [← re_weilFunction_sub_re_logDeriv_xi hW hσ t, re_logDeriv_xi_eq_tsum_copyPoisson hσ t]
  obtain ⟨hsC, hC⟩ := tsum_carried_le hW hσ t
  have hsA := summable_copyPoisson hσ t
  have hsD : Summable fun q => deficitWeight hW q * copyPoisson σ t q :=
    hsA.of_nonneg_of_le (fun q => mul_nonneg (deficitWeight_nonneg hW q)
      (copyPoisson_pos hσ.le t q).le) fun q => by
      have := mul_le_mul_of_nonneg_right (deficitWeight_le_one hW q) (copyPoisson_pos hσ.le t q).le
      linarith
  have hterm : ∀ q, copyPoisson σ t q - carriedWeight hW q * copyPoisson σ t q ≤
      deficitWeight hW q * copyPoisson σ t q := by
    intro q
    have := mul_le_mul_of_nonneg_right (one_sub_le hW q) (copyPoisson_pos hσ.le t q).le
    linarith
  have hle : (∑' q, copyPoisson σ t q) - ∑' q, carriedWeight hW q * copyPoisson σ t q ≤
      deficitEnvelope hW σ t := by
    rw [← hsA.tsum_sub hsC]
    exact (hsA.sub hsC).tsum_le_tsum hterm hsD
  linarith

/-- **Bohr envelope bound along a sequence.**  As `CosineSeriesBohrEnvelope`, but the Cesàro mean of
`ε` need only be at most `E + η` along arbitrarily large `T`, for every `η > 0`. -/
theorem abs_le_four_mul_of_logCosSeries_envelope_frequently {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) (ha0 : a 0 = 0) (ha1 : a 1 = 0) {ε : ℝ → ℝ}
    (hε0 : ∀ t, 0 ≤ ε t) (hεc : Continuous ε) {E : ℝ}
    (hE : ∀ η > 0, ∃ᶠ T in atTop, (∫ t in (8 : ℝ)..T, ε t) / T ≤ E + η)
    (hf : ∀ t, 8 ≤ t → -ε t ≤ logCosSeries a t) {m : ℕ} (hm : 2 ≤ m) : |a m| ≤ 4 * E := by
  have hcont := continuous_logCosSeries ha
  have hg := tendsto_mean_logCosSeries_mul_cos ha m
  rw [bohrLimit_eq_coeff ha0 hm] at hg
  have hF := tendsto_mean_logCosSeries_mul_cos ha 1
  rw [bohrLimit_one_eq_zero ha0 ha1] at hF
  have hF' : Tendsto (fun T : ℝ => (∫ t in (8 : ℝ)..T, logCosSeries a t) / T) atTop (𝓝 0) := by
    refine hF.congr' (Eventually.of_forall fun T => ?_)
    simp
  have hbound : ∀ᶠ T in atTop, |(∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)) / T|
      ≤ (∫ t in (8 : ℝ)..T, logCosSeries a t) / T + 2 * ((∫ t in (8 : ℝ)..T, ε t) / T) := by
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hint1 : IntervalIntegrable (fun t => logCosSeries a t * Real.cos (t * Real.log m))
        volume 8 T := (hcont.mul (by fun_prop)).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (logCosSeries a) volume 8 T := hcont.intervalIntegrable _ _
    have hint3 : IntervalIntegrable ε volume 8 T := hεc.intervalIntegrable _ _
    have hpt : ∀ t ∈ Set.Icc (8 : ℝ) T,
        |logCosSeries a t * Real.cos (t * Real.log m)| ≤ logCosSeries a t + 2 * ε t := by
      intro t ht
      have h1 := hf t ht.1
      have h2 := hε0 t
      rw [abs_mul]
      have h3 := Real.abs_cos_le_one (t * Real.log m)
      have h4 : |logCosSeries a t| ≤ logCosSeries a t + 2 * ε t := by
        rcases le_or_gt 0 (logCosSeries a t) with h | h
        · rw [abs_of_nonneg h]; linarith
        · rw [abs_of_neg h]; linarith
      calc |logCosSeries a t| * |Real.cos (t * Real.log m)| ≤ |logCosSeries a t| * 1 :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ ≤ _ := by linarith
    have hI : |∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)| ≤
        (∫ t in (8 : ℝ)..T, logCosSeries a t) + 2 * ∫ t in (8 : ℝ)..T, ε t := by
      calc |∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)|
          ≤ ∫ t in (8 : ℝ)..T, |logCosSeries a t * Real.cos (t * Real.log m)| :=
            intervalIntegral.abs_integral_le_integral_abs hT
        _ ≤ ∫ t in (8 : ℝ)..T, (logCosSeries a t + 2 * ε t) :=
            intervalIntegral.integral_mono_on hT hint1.abs (hint2.add (hint3.const_mul 2)) hpt
        _ = (∫ t in (8 : ℝ)..T, logCosSeries a t) + 2 * ∫ t in (8 : ℝ)..T, ε t := by
            rw [intervalIntegral.integral_add hint2 (hint3.const_mul 2),
              intervalIntegral.integral_const_mul]
    rw [abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
    have : ((∫ t in (8 : ℝ)..T, logCosSeries a t) / T + 2 * ((∫ t in (8 : ℝ)..T, ε t) / T)) * T =
        (∫ t in (8 : ℝ)..T, logCosSeries a t) + 2 * ∫ t in (8 : ℝ)..T, ε t := by
      field_simp
    rw [this]
    exact hI
  -- along the frequent sequence the bound gives `|a m|/2 ≤ 2(E + η)`
  have hηb : ∀ η > 0, |a m| / 2 ≤ 2 * (E + η) := by
    intro η hη
    have hlimg := hg.abs
    rw [abs_div, abs_two] at hlimg
    by_contra hcon
    push Not at hcon
    -- eventually the left side exceeds `2(E + η) + δ` and the mean of the series is small
    set δ := (|a m| / 2 - 2 * (E + η)) / 3 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have h1 : ∀ᶠ T in atTop, |a m| / 2 - δ <
        |(∫ t in (8 : ℝ)..T, logCosSeries a t * Real.cos (t * Real.log m)) / T| :=
      hlimg.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ T in atTop, (∫ t in (8 : ℝ)..T, logCosSeries a t) / T < δ :=
      hF'.eventually (gt_mem_nhds hδ0)
    obtain ⟨T, ⟨⟨hT1, hT2⟩, hT3⟩, hT4⟩ :=
      (((h1.and h2).and hbound).and_frequently (hE η hη)).exists
    have : |a m| / 2 - δ < δ + 2 * (E + η) := by linarith
    rw [hδ] at this
    linarith
  -- let `η → 0`
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have := hηb (η / 8) (by positivity)
  linarith

/-! ## The singular deficit law -/

theorem abs_deviationCoeff {lam : ℕ → ℝ} {σ : ℝ} {m : ℕ} (hm : 2 ≤ m) :
    |deviationCoeff lam σ m| = |lam m - ArithmeticFunction.vonMangoldt m| * (m : ℝ) ^ (-σ) := by
  have hpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [deviationCoeff, if_pos hm, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _), abs_sub_comm]

/-- **The singular deficit law (envelope form).**  For a full-cone Weil-positive `lam` and
`σ > 1`: if the Cesàro mean of the deficit envelope `ε_σ` is at most `E + η` along arbitrarily
large `T` for every `η > 0`, then `|lam(m) − Λ(m)| m^{−σ} ≤ 4E` for all `m ≥ 2`. -/
theorem abs_sub_vonMangoldt_le_of_envelope {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ}
    (hσ : 1 < σ) {E : ℝ}
    (hE : ∀ η > 0, ∃ᶠ T in atTop, (∫ t in (8 : ℝ)..T, deficitEnvelope hW σ t) / T ≤ E + η)
    {m : ℕ} (hm : 2 ≤ m) :
    |lam m - ArithmeticFunction.vonMangoldt m| * (m : ℝ) ^ (-σ) ≤ 4 * E := by
  rw [← abs_deviationCoeff hm]
  exact abs_le_four_mul_of_logCosSeries_envelope_frequently
    (summable_abs_deviationCoeff hW hσ) (by simp [deviationCoeff]) (by simp [deviationCoeff])
    (deficitEnvelope_nonneg hW hσ) (continuous_deficitEnvelope hW hσ) hE
    (fun t _ => neg_deficitEnvelope_le hW hσ t) hm

/-- **Sparse repair is impossible (envelope form).**  If the deficit envelope has Cesàro mean
tending to `0` along a sequence, for some `σ > 1`, then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_envelope_mean_tendsto_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ)
    (hE : ∀ η > 0, ∃ᶠ T in atTop, (∫ t in (8 : ℝ)..T, deficitEnvelope hW σ t) / T ≤ η) :
    ∀ m : ℕ, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  intro m hm
  have h := abs_sub_vonMangoldt_le_of_envelope hW hσ (E := 0)
    (fun η hη => by simpa using hE η hη) hm
  have hpos : (0 : ℝ) < (m : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < m)) _
  have : |lam m - ArithmeticFunction.vonMangoldt m| = 0 := by
    have h0 : |lam m - ArithmeticFunction.vonMangoldt m| * (m : ℝ) ^ (-σ) ≤ 0 := by simpa using h
    have := mul_nonneg (abs_nonneg (lam m - ArithmeticFunction.vonMangoldt m)) hpos.le
    nlinarith
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

end RHTower.WeilSpectral

end
