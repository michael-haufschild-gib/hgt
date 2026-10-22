import GaloisForLFunctions.RHTower.ThetaChronologicalSingularDeconvolution
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalL1Translation
import GaloisForLFunctions.RHTower.RouteECofactorSquarefreeHarmonic
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Literal opposite-sign Möbius packets defeat compact regular observers

For an odd prime `q` put `m = 2q` and let `p` be the least prime above `m`; then `μ(m) = +1`,
`μ(p) = −1`, and the prime number theorem gives `δ_q = log(p/m) → 0`.  The literal two-atom
submeasure `λ_{q,σ} = m^{−1−σ} δ_{−log m} − p^{−1−σ} δ_{−log p}` of `ν_σ` has total variation
`A + B`, and

* `‖λ * ψ‖₁ ≤ |A − B| ‖ψ‖₁ + B ‖ψ − ψ(· + δ)‖₁` (22);
* for every compact `K ⊂ L¹(ℝ)`, `sup_{ψ ∈ K} ‖λ_{q,σ} * ψ‖₁ / ‖λ_{q,σ}‖_TV → 0` (21);
* with a `W^{1,1}` kernel, the ratio is at most `δ_q/2 ((1+σ)‖ψ‖₁ + ‖ψ'‖₁)` (23), so separating
  the packets by a fixed fraction `c` forces `‖ψ_q'‖₁ ≥ 2c/δ_q − (1+σ)M` (24).

Up to scale `X` there are `O(X/log X)` packets against `X/ζ(2) + o(X)` squarefree sites, and the
half-power packet weight is `O(√X/log X)` against order `√X`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace RHTower

noncomputable section

/-! ## (20) The packets -/

/-- The least prime strictly greater than `2q`. -/
def packetPrime (q : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (2 * q + 1))

theorem packetPrime_spec (q : ℕ) : 2 * q + 1 ≤ packetPrime q ∧ (packetPrime q).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (2 * q + 1))

theorem packetPrime_prime (q : ℕ) : (packetPrime q).Prime := (packetPrime_spec q).2

theorem two_mul_lt_packetPrime (q : ℕ) : 2 * q < packetPrime q := (packetPrime_spec q).1

/-- Minimality: `p` is the least prime above `2q`. -/
theorem packetPrime_le {q r : ℕ} (hr : r.Prime) (h : 2 * q < r) : packetPrime q ≤ r :=
  Nat.find_min' _ ⟨h, hr⟩

/-- `μ(2q) = +1` for an odd prime `q`. -/
theorem moebius_two_mul_of_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ArithmeticFunction.moebius (2 * q) = 1 := by
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two, ArithmeticFunction.moebius_apply_prime hq]
  norm_num

/-- `μ(p) = −1`. -/
theorem moebius_packetPrime (q : ℕ) : ArithmeticFunction.moebius (packetPrime q) = -1 :=
  ArithmeticFunction.moebius_apply_prime (packetPrime_prime q)

/-- The logarithmic packet gap `δ_q = log(p/m)`. -/
def packetGap (q : ℕ) : ℝ := Real.log (packetPrime q) - Real.log ((2 * q : ℕ) : ℝ)

theorem packetGap_pos {q : ℕ} (hq : 0 < q) : 0 < packetGap q := by
  rw [packetGap, sub_pos]
  exact Real.log_lt_log (by exact_mod_cast (by omega : 0 < 2 * q)) (by exact_mod_cast two_mul_lt_packetPrime q)

/-- **The prime number theorem places `p` just above `m`:** `p/m → 1`. -/
theorem tendsto_packetPrime_div :
    Tendsto (fun q : ℕ => (packetPrime q : ℝ) / ((2 * q : ℕ) : ℝ)) atTop (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with q hq
    have hm : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
    rw [lt_div_iff₀ hm]
    have : ((2 * q : ℕ) : ℝ) < packetPrime q := by exact_mod_cast two_mul_lt_packetPrime q
    nlinarith
  · have hε : 0 < a - 1 := by linarith
    have hmto : Tendsto (fun q : ℕ => ((2 * q : ℕ) : ℝ)) atTop atTop := by
      have : Tendsto (fun q : ℕ => 2 * q) atTop atTop :=
        tendsto_id.const_mul_atTop' (by norm_num)
      exact tendsto_natCast_atTop_atTop.comp this
    filter_upwards [hmto.eventually (prime_between hε), eventually_gt_atTop 0] with q hq hq0
    obtain ⟨r, hr, hr1, hr2⟩ := hq
    have hm : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
    have hle : (packetPrime q : ℝ) ≤ r := by
      exact_mod_cast packetPrime_le hr (by exact_mod_cast hr1)
    rw [div_lt_iff₀ hm]
    nlinarith

/-- **`δ_q → 0`.** -/
theorem tendsto_packetGap : Tendsto packetGap atTop (𝓝 0) := by
  have h := ((Real.continuousAt_log one_ne_zero).tendsto).comp tendsto_packetPrime_div
  rw [Real.log_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with q hq
  have hm : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  have hp : (0 : ℝ) < packetPrime q := by exact_mod_cast (packetPrime_prime q).pos
  simp only [Function.comp, packetGap]
  rw [Real.log_div hp.ne' hm.ne']

/-- The packet weights `A = m^{−1−σ}`, `B = p^{−1−σ}`. -/
def packetWeightA (σ : ℝ) (q : ℕ) : ℝ := ((2 * q : ℕ) : ℝ) ^ (-(1 + σ))

def packetWeightB (σ : ℝ) (q : ℕ) : ℝ := (packetPrime q : ℝ) ^ (-(1 + σ))

theorem packetWeightA_pos (σ : ℝ) {q : ℕ} (hq : 0 < q) : 0 < packetWeightA σ q :=
  Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < 2 * q)) _

theorem packetWeightB_pos (σ : ℝ) (q : ℕ) : 0 < packetWeightB σ q :=
  Real.rpow_pos_of_pos (by exact_mod_cast (packetPrime_prime q).pos) _

/-- **`λ_{q,σ}` is a literal two-atom submeasure of `ν_σ`:** its atoms are those of `ν_σ`. -/
theorem deconvMeasure_packet_atoms (σ : ℝ) [Fact (0 < σ)] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    deconvMeasure σ {deconvSite (2 * q)} = packetWeightA σ q ∧
      deconvMeasure σ {deconvSite (packetPrime q)} = -packetWeightB σ q := by
  refine ⟨?_, ?_⟩
  · rw [deconvMeasure_singleton σ (by have := hq.pos; omega), deconvWeight,
      moebius_two_mul_of_prime hq hq2, packetWeightA]
    norm_num
  · rw [deconvMeasure_singleton σ (packetPrime_prime q).pos, deconvWeight, moebius_packetPrime,
      packetWeightB]
    norm_num

/-- The Jordan decomposition of `λ_{q,σ} = A δ_{−log m} − B δ_{−log p}`. -/
def packetJordan (σ : ℝ) (q : ℕ) (hq : 0 < q) : JordanDecomposition ℝ where
  posPart := ENNReal.ofReal (packetWeightA σ q) • Measure.dirac (deconvSite (2 * q))
  negPart := ENNReal.ofReal (packetWeightB σ q) • Measure.dirac (deconvSite (packetPrime q))
  mutuallySingular := by
    refine ⟨{deconvSite (2 * q)}ᶜ, (measurableSet_singleton _).compl, ?_, ?_⟩
    · rw [Measure.smul_apply, Measure.dirac_apply]; simp
    · rw [compl_compl, Measure.smul_apply, Measure.dirac_apply]
      have : deconvSite (packetPrime q) ∉ ({deconvSite (2 * q)} : Set ℝ) := fun h =>
        absurd (deconvSite_inj (packetPrime_prime q).pos (by omega) h)
          (two_mul_lt_packetPrime q).ne'
      simp [this]

/-- **`‖λ_{q,σ}‖_TV = A + B`.** -/
theorem packet_totalVariation (σ : ℝ) {q : ℕ} (hq : 0 < q) :
    ((packetJordan σ q hq).toSignedMeasure.totalVariation univ).toReal =
      packetWeightA σ q + packetWeightB σ q := by
  rw [SignedMeasure.totalVariation, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  simp only [packetJordan, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (packetWeightA_pos σ hq).le, ENNReal.toReal_ofReal (packetWeightB_pos σ q).le]

/-! ## (22) The two-atom estimate -/

/-- **(22)** `∫ |A ψ(y + a) − B ψ(y + b)| ≤ |A − B| ‖ψ‖₁ + B ‖ψ − ψ(· + (b − a))‖₁`. -/
theorem integral_abs_twoAtom_le {ψ : ℝ → ℝ} (hψ : Integrable ψ) (A B a b : ℝ) (hB : 0 ≤ B) :
    (∫ y, |A * ψ (y + a) - B * ψ (y + b)|) ≤
      |A - B| * (∫ y, |ψ y|) + B * ∫ y, |ψ y - ψ (y + (b - a))| := by
  have hshift : (∫ y, |A * ψ (y + a) - B * ψ (y + b)|) = ∫ u, |A * ψ u - B * ψ (u + (b - a))| := by
    rw [← integral_add_right_eq_self (μ := volume) (fun u => |A * ψ u - B * ψ (u + (b - a))|) a]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    congr 3; ring_nf
  have h1 : Integrable fun u => |A - B| * |ψ u| := hψ.abs.const_mul _
  have h2 : Integrable fun u => B * |ψ u - ψ (u + (b - a))| :=
    (hψ.sub (hψ.comp_add_right (b - a))).abs.const_mul _
  rw [hshift, ← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  refine integral_mono ((hψ.const_mul A).sub ((hψ.comp_add_right (b - a)).const_mul B)).abs (h1.add h2)
    fun u => ?_
  have : A * ψ u - B * ψ (u + (b - a)) = (A - B) * ψ u + B * (ψ u - ψ (u + (b - a))) := by ring
  rw [this]
  refine (abs_add_le _ _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg hB]

/-! ## (23)–(24) The `W^{1,1}` resolution cost -/

/-- `sinh x ≤ x cosh x` for `x ≥ 0`, i.e. `tanh x ≤ x`. -/
theorem exp_sub_exp_neg_le_mul {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - Real.exp (-x) ≤ x * (Real.exp x + Real.exp (-x)) := by
  set h : ℝ → ℝ := fun x => x * (Real.exp x + Real.exp (-x)) - (Real.exp x - Real.exp (-x))
  have hd : ∀ x, HasDerivAt h (x * (Real.exp x - Real.exp (-x))) x := by
    intro x
    have he := Real.hasDerivAt_exp x
    have hen : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-x)) x := by
      have := (hasDerivAt_neg x).exp
      simpa using this
    have := ((hasDerivAt_id x).fun_mul (he.fun_add hen)).fun_sub (he.fun_sub hen)
    exact this.congr_deriv (by simp only [id]; ring)
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have hx' : 0 < x := hx
    exact mul_nonneg hx'.le (sub_nonneg.2 (Real.exp_le_exp.2 (by linarith)))
  have := hmono (self_mem_Ici) hx hx
  simp only [h, neg_zero, Real.exp_zero, zero_mul, sub_self] at this
  linarith

/-- **`|A − B|/(A + B) = tanh((1+σ)δ/2) ≤ (1+σ)δ/2`** for `A = m^{−s}`, `B = p^{−s}`, `m ≤ p`. -/
theorem rpow_neg_sub_div_add_le {m p s : ℝ} (hm : 0 < m) (hmp : m ≤ p) (hs : 0 ≤ s) :
    (m ^ (-s) - p ^ (-s)) / (m ^ (-s) + p ^ (-s)) ≤ s * (Real.log p - Real.log m) / 2 := by
  have hp : 0 < p := lt_of_lt_of_le hm hmp
  set x : ℝ := s * (Real.log p - Real.log m) / 2
  have hx : 0 ≤ x := by
    have := Real.log_le_log hm hmp
    positivity
  set c : ℝ := Real.exp (s * (Real.log m + Real.log p) / 2)
  have hc : 0 < c := Real.exp_pos _
  have hA : m ^ (-s) * c = Real.exp x := by
    rw [Real.rpow_def_of_pos hm, ← Real.exp_add]; congr 1; simp only [x]; ring
  have hB : p ^ (-s) * c = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos hp, ← Real.exp_add]; congr 1; simp only [x]; ring
  have hden : 0 < m ^ (-s) + p ^ (-s) := by positivity
  rw [div_le_iff₀ hden]
  have key := exp_sub_exp_neg_le_mul hx
  rw [← hA, ← hB] at key
  nlinarith

/-- **(23)** With `ψ ∈ W^{1,1}`, `‖λ * ψ‖₁ / ‖λ‖_TV ≤ δ/2 ((1+σ)‖ψ‖₁ + ‖ψ'‖₁)`, `δ = log(p/m)`. -/
theorem twoAtom_ratio_le {ψ : ℝ → ℝ} (hψ : Integrable ψ) (hψd : Differentiable ℝ ψ)
    (hψc : Continuous (deriv ψ)) (hψ' : Integrable (deriv ψ)) {m p σ : ℝ} (hm : 0 < m) (hmp : m ≤ p)
    (hσ : 0 ≤ 1 + σ) :
    (∫ y, |m ^ (-(1 + σ)) * ψ (y + Real.log m) - p ^ (-(1 + σ)) * ψ (y + Real.log p)|) /
        (m ^ (-(1 + σ)) + p ^ (-(1 + σ))) ≤
      (Real.log p - Real.log m) / 2 * ((1 + σ) * (∫ y, |ψ y|) + ∫ y, |deriv ψ y|) := by
  have hp : 0 < p := lt_of_lt_of_le hm hmp
  set A := m ^ (-(1 + σ))
  set B := p ^ (-(1 + σ))
  set δ := Real.log p - Real.log m
  have hδ : 0 ≤ δ := sub_nonneg.2 (Real.log_le_log hm hmp)
  have hA : 0 < A := Real.rpow_pos_of_pos hm _
  have hB : 0 < B := Real.rpow_pos_of_pos hp _
  have hAB : B ≤ A := Real.rpow_le_rpow_of_nonpos hm hmp (by linarith)
  have h22 := integral_abs_twoAtom_le hψ A B (Real.log m) (Real.log p) hB.le
  have htrans : (∫ y, |ψ y - ψ (y + δ)|) ≤ δ * ∫ y, |deriv ψ y| := by
    have h := GaloisForLFunctions.HTGeometry.integral_norm_translation_le ψ hψd hψc hψ' hδ
      ((hψ.comp_add_right δ).sub hψ).norm
    simp only [Real.norm_eq_abs] at h
    calc (∫ y, |ψ y - ψ (y + δ)|) = ∫ y, |ψ (y + δ) - ψ y| :=
          integral_congr_ae (Eventually.of_forall fun y => abs_sub_comm _ _)
      _ ≤ _ := h
  have htanh : (A - B) / (A + B) ≤ (1 + σ) * δ / 2 := rpow_neg_sub_div_add_le hm hmp hσ
  have hhalf : B / (A + B) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hI0 : 0 ≤ ∫ y, |ψ y| := integral_nonneg fun _ => abs_nonneg _
  have hD0 : 0 ≤ ∫ y, |deriv ψ y| := integral_nonneg fun _ => abs_nonneg _
  rw [div_le_iff₀ (by positivity)]
  refine h22.trans ?_
  rw [abs_of_nonneg (by linarith : 0 ≤ A - B)]
  have e1 : (A - B) * (∫ y, |ψ y|) ≤ (1 + σ) * δ / 2 * (A + B) * ∫ y, |ψ y| := by
    have := (div_le_iff₀ (by positivity : 0 < A + B)).1 htanh
    exact mul_le_mul_of_nonneg_right this hI0
  have e2 : B * (∫ y, |ψ y - ψ (y + (Real.log p - Real.log m))|) ≤ 1 / 2 * (A + B) * (δ * ∫ y, |deriv ψ y|) := by
    have := (div_le_iff₀ (by positivity : 0 < A + B)).1 hhalf
    exact mul_le_mul this htrans (integral_nonneg fun _ => abs_nonneg _) (by positivity)
  nlinarith

/-- **(24) Resolution cost.**  If a kernel with `‖ψ‖₁ ≤ M` separates a packet by a fraction `c` of
its total variation, then `‖ψ'‖₁ ≥ 2c/δ − (1+σ)M`. -/
theorem deriv_norm_ge_of_separation {ψ : ℝ → ℝ} (hψ : Integrable ψ) (hψd : Differentiable ℝ ψ)
    (hψc : Continuous (deriv ψ)) (hψ' : Integrable (deriv ψ)) {m p σ c M : ℝ} (hm : 0 < m)
    (hmp : m < p) (hσ : 0 ≤ 1 + σ) (hM : (∫ y, |ψ y|) ≤ M)
    (hsep : c ≤ (∫ y, |m ^ (-(1 + σ)) * ψ (y + Real.log m) - p ^ (-(1 + σ)) * ψ (y + Real.log p)|) /
        (m ^ (-(1 + σ)) + p ^ (-(1 + σ)))) :
    2 * c / (Real.log p - Real.log m) - (1 + σ) * M ≤ ∫ y, |deriv ψ y| := by
  have hδ : 0 < Real.log p - Real.log m := sub_pos.2 (Real.log_lt_log hm hmp)
  have h := hsep.trans (twoAtom_ratio_le hψ hψd hψc hψ' hm hmp.le hσ)
  rw [sub_le_iff_le_add, div_le_iff₀ hδ]
  have : (1 + σ) * (∫ y, |ψ y|) ≤ (1 + σ) * M := mul_le_mul_of_nonneg_left hM hσ
  nlinarith

/-! ## (21) Compact families of regular kernels -/

/-- Translation `τ_t ψ = ψ(t + ·)` on real `L¹`. -/
def realL1Shift (t : ℝ) (f : Lp ℝ 1 (volume : Measure ℝ)) : Lp ℝ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (realAddTranslationFamily t) (measurePreserving_realAddTranslationFamily t) f

theorem realL1Shift_ae (t : ℝ) (f : Lp ℝ 1 (volume : Measure ℝ)) :
    (realL1Shift t f : ℝ → ℝ) =ᵐ[volume] fun x => f (t + x) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_realAddTranslationFamily t)] with x hx
  simpa only [realL1Shift, Function.comp_apply, realAddTranslationFamily_apply] using hx

theorem continuous_realL1Shift_joint :
    Continuous fun p : ℝ × Lp ℝ 1 (volume : Measure ℝ) => realL1Shift p.1 p.2 :=
  continuous_snd.compMeasurePreservingLp (realAddTranslationFamily.continuous.comp continuous_fst)
    (fun p => measurePreserving_realAddTranslationFamily p.1) (by norm_num)

theorem realL1Shift_zero (f : Lp ℝ 1 (volume : Measure ℝ)) : realL1Shift 0 f = f := by
  refine Lp.ext ?_
  filter_upwards [realL1Shift_ae 0 f] with x hx
  rw [hx, zero_add]

/-- **Translations are uniformly continuous on compact subsets of `L¹`.** -/
theorem eventually_forall_norm_realL1Shift_sub_lt {K : Set (Lp ℝ 1 (volume : Measure ℝ))}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ ψ ∈ K, ‖realL1Shift t ψ - ψ‖ < ε := by
  refine hK.eventually_forall_of_forall_eventually fun ψ _ => ?_
  have hc : Continuous fun p : ℝ × Lp ℝ 1 (volume : Measure ℝ) => realL1Shift p.1 p.2 - p.2 :=
    continuous_realL1Shift_joint.sub continuous_snd
  have h := (hc.continuousAt (x := ((0 : ℝ), ψ))).eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [h] with p hp
  rwa [realL1Shift_zero, sub_self, dist_zero_right] at hp

theorem norm_twoShift_eq (A B a b : ℝ) (ψ : Lp ℝ 1 (volume : Measure ℝ)) :
    ‖A • realL1Shift a ψ - B • realL1Shift b ψ‖ = ∫ y, |A * ψ (y + a) - B * ψ (y + b)| := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (A • realL1Shift a ψ) (B • realL1Shift b ψ),
    Lp.coeFn_smul A (realL1Shift a ψ), Lp.coeFn_smul B (realL1Shift b ψ), realL1Shift_ae a ψ,
    realL1Shift_ae b ψ] with y h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, smul_eq_mul, smul_eq_mul,
    Real.norm_eq_abs, add_comm a, add_comm b]

theorem norm_shift_sub_eq (t : ℝ) (ψ : Lp ℝ 1 (volume : Measure ℝ)) :
    ‖realL1Shift t ψ - ψ‖ = ∫ y, |ψ y - ψ (y + t)| := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (realL1Shift t ψ) ψ, realL1Shift_ae t ψ] with y h1 h2
  rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs, abs_sub_comm, add_comm t]

theorem norm_eq_integral_abs (ψ : Lp ℝ 1 (volume : Measure ℝ)) : ‖ψ‖ = ∫ y, |ψ y| := by
  rw [L1.norm_eq_integral_norm]; rfl

/-- **(21) Compact regular observers cannot resolve the literal packets.**  For every compact
`K ⊂ L¹(ℝ)` and `ε > 0`, eventually in `q`, every `ψ ∈ K` has
`‖λ_{q,σ} * ψ‖₁ ≤ ε ‖λ_{q,σ}‖_TV`, where `(λ_{q,σ} * ψ)(y) = A ψ(y + log m) − B ψ(y + log p)`. -/
theorem packet_conv_le_of_isCompact {σ : ℝ} (hσ : 0 ≤ 1 + σ) {K : Set (Lp ℝ 1 (volume : Measure ℝ))}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ ψ ∈ K,
      ‖packetWeightA σ q • realL1Shift (Real.log ((2 * q : ℕ) : ℝ)) ψ -
          packetWeightB σ q • realL1Shift (Real.log (packetPrime q)) ψ‖ ≤
        ε * (packetWeightA σ q + packetWeightB σ q) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hR0 : ∀ ψ ∈ K, 0 ≤ R := fun ψ hψ => (norm_nonneg ψ).trans (hR ψ hψ)
  have hshift := tendsto_packetGap.eventually (eventually_forall_norm_realL1Shift_sub_lt hK
    (half_pos hε))
  have hsmall : ∀ᶠ q : ℕ in atTop, (1 + σ) * packetGap q / 2 * |R| ≤ ε / 2 := by
    have h := ((tendsto_packetGap.const_mul ((1 + σ) / 2)).mul_const |R|)
    simp only [mul_zero, zero_mul] at h
    filter_upwards [h.eventually (ge_mem_nhds (half_pos hε))] with q hq
    calc (1 + σ) * packetGap q / 2 * |R| = (1 + σ) / 2 * packetGap q * |R| := by ring
      _ ≤ ε / 2 := hq
  filter_upwards [hshift, hsmall, eventually_gt_atTop 0] with q hq1 hq2 hq0 ψ hψ
  set A := packetWeightA σ q
  set B := packetWeightB σ q
  have hA := packetWeightA_pos σ hq0
  have hB := packetWeightB_pos σ q
  have hm : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  have hmp : ((2 * q : ℕ) : ℝ) ≤ packetPrime q := by exact_mod_cast (two_mul_lt_packetPrime q).le
  have hAB : B ≤ A := Real.rpow_le_rpow_of_nonpos hm hmp (by linarith)
  have htanh : (A - B) / (A + B) ≤ (1 + σ) * packetGap q / 2 := rpow_neg_sub_div_add_le hm hmp hσ
  have h22 := integral_abs_twoAtom_le (L1.integrable_coeFn ψ) A B (Real.log ((2 * q : ℕ) : ℝ))
    (Real.log (packetPrime q)) hB.le
  rw [norm_twoShift_eq]
  refine h22.trans ?_
  have hδ : Real.log (packetPrime q) - Real.log ((2 * q : ℕ) : ℝ) = packetGap q := rfl
  rw [hδ, ← norm_shift_sub_eq, ← norm_eq_integral_abs, abs_of_nonneg (by linarith : 0 ≤ A - B)]
  have hψR : ‖ψ‖ ≤ |R| := (hR ψ hψ).trans (le_abs_self R)
  have e1 : (A - B) * ‖ψ‖ ≤ (A + B) * (ε / 2) := by
    have h1 : A - B ≤ (1 + σ) * packetGap q / 2 * (A + B) := (div_le_iff₀ (by positivity)).1 htanh
    have hg : 0 ≤ (1 + σ) * packetGap q / 2 := by
      have := (packetGap_pos hq0).le; positivity
    calc (A - B) * ‖ψ‖ ≤ ((1 + σ) * packetGap q / 2 * (A + B)) * |R| :=
          mul_le_mul h1 hψR (norm_nonneg _) (by positivity)
      _ = (A + B) * ((1 + σ) * packetGap q / 2 * |R|) := by ring
      _ ≤ (A + B) * (ε / 2) := mul_le_mul_of_nonneg_left hq2 (by positivity)
  have e2 : B * ‖realL1Shift (packetGap q) ψ - ψ‖ ≤ (A + B) * (ε / 2) :=
    mul_le_mul (by linarith) (hq1 ψ hψ).le (norm_nonneg _) (by positivity)
  linarith

/-- **(18), weighted form.**  With the coefficient weights `(n+1)^{−1−σ}, (n+2)^{−1−σ}` of adjacent
sites the ratio `‖λ * φ_σ‖₁ / ‖λ‖_TV` still tends to zero. -/
theorem tendsto_weighted_adjacent_ratio {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun n : ℕ =>
      (∫ y, |((n : ℝ) + 1) ^ (-(1 + σ)) * weightedCutoffAtom σ (y + Real.log ((n : ℝ) + 1)) -
          ((n : ℝ) + 2) ^ (-(1 + σ)) * weightedCutoffAtom σ (y + Real.log ((n : ℝ) + 2))|) /
        (((n : ℝ) + 1) ^ (-(1 + σ)) + ((n : ℝ) + 2) ^ (-(1 + σ)))) atTop (𝓝 0) := by
  set f := weightedCutoffAtom σ
  have hfd : Differentiable ℝ f := fun y => (hasDerivAt_weightedAtom σ _ y).differentiableAt
  have hderiv := deriv_weightedAtom σ cutoffAtomPoly
  have hfc : Continuous (deriv f) := by
    show Continuous (deriv (weightedAtom σ cutoffAtomPoly)); rw [hderiv]; exact continuous_weightedAtom _ _
  have hfi' : Integrable (deriv f) := by
    show Integrable (deriv (weightedAtom σ cutoffAtomPoly)); rw [hderiv]
    exact integrable_weightedAtom _ (by linarith)
  have hfi : Integrable f := integrable_weightedAtom _ (by linarith)
  set D : ℝ := (1 + σ) * (∫ y, |f y|) + ∫ y, |deriv f y|
  have hbound : ∀ n : ℕ, 0 ≤ (∫ y, |((n : ℝ) + 1) ^ (-(1 + σ)) * f (y + Real.log ((n : ℝ) + 1)) -
          ((n : ℝ) + 2) ^ (-(1 + σ)) * f (y + Real.log ((n : ℝ) + 2))|) /
        (((n : ℝ) + 1) ^ (-(1 + σ)) + ((n : ℝ) + 2) ^ (-(1 + σ))) ∧
      (∫ y, |((n : ℝ) + 1) ^ (-(1 + σ)) * f (y + Real.log ((n : ℝ) + 1)) -
          ((n : ℝ) + 2) ^ (-(1 + σ)) * f (y + Real.log ((n : ℝ) + 2))|) /
        (((n : ℝ) + 1) ^ (-(1 + σ)) + ((n : ℝ) + 2) ^ (-(1 + σ))) ≤
      (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) / 2 * D := fun n =>
    ⟨div_nonneg (integral_nonneg fun _ => abs_nonneg _) (by positivity),
      twoAtom_ratio_le hfi hfd hfc hfi' (by positivity) (by linarith) (by linarith)⟩
  have hlim : Tendsto (fun n : ℕ => (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) / 2 * D) atTop (𝓝 0) := by
    simpa using (tendsto_log_add_two_sub_log_add_one.div_const 2).mul_const D
  exact squeeze_zero (fun n => (hbound n).1) (fun n => (hbound n).2) hlim

/-! ## The counting remark -/

theorem natCast_rpow_neg_half_eq (x : ℕ) : (x : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg x)]

/-- **Chebyshev-weighted half sum.**  `Σ_{p ≤ N} log p · p^{−1/2} ≤ 8 √N`. -/
theorem sum_primesLE_log_mul_rpow_neg_half_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 8 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set M := N / 2
  have hMN : M < N := Nat.div_lt_self hN (by norm_num)
  rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE N) (fun p => p ≤ M)]
  have hlow : (Nat.primesLE N).filter (fun p => p ≤ M) = Nat.primesLE M := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hp⟩, hpM⟩; exact ⟨hpM, hp⟩
    · rintro ⟨hpM, hp⟩; exact ⟨⟨hpM.trans (Nat.div_le_self _ _), hp⟩, hpM⟩
  rw [hlow]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hs2 : 0 < Real.sqrt 2 := by positivity
  set L : ℝ := Real.log 4
  have hhigh : ∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ M),
      Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 * L * Real.sqrt N := by
    have hpt : ∀ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ M),
        Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.log p * (Real.sqrt 2 / Real.sqrt N) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      have hpp := hp.1.2.pos
      have hp2 : (N : ℝ) / 2 ≤ p := by
        have : N < 2 * p := by omega
        have : (N : ℝ) < 2 * p := by exact_mod_cast this
        linarith
      refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by exact_mod_cast hpp))
      rw [natCast_rpow_neg_half_eq]
      calc (Real.sqrt p)⁻¹ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ :=
            inv_anti₀ (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt hp2)
        _ = Real.sqrt 2 / Real.sqrt N := by rw [Real.sqrt_div hNR.le, inv_div]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_mul]
    have htheta : ∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ M), Real.log p ≤ L * N := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun p hp _ => Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le)) ?_
      rw [← Chebyshev.theta_eq_sum_primesLE_log]
      exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
    have hL : 0 ≤ L := Real.log_nonneg (by norm_num)
    calc (∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ M), Real.log p) * (Real.sqrt 2 / Real.sqrt N)
        ≤ L * N * (Real.sqrt 2 / Real.sqrt N) := mul_le_mul_of_nonneg_right htheta (by positivity)
      _ = Real.sqrt 2 * L * Real.sqrt N := by
          have h := Real.mul_self_sqrt hNR.le
          rw [mul_div_assoc', div_eq_iff hsN.ne']
          linear_combination (-(Real.sqrt 2 * L)) * h
  have h1 := ih M hMN
  have hM2 : Real.sqrt M ≤ Real.sqrt N / Real.sqrt 2 := by
    rw [← Real.sqrt_div hNR.le]
    exact Real.sqrt_le_sqrt (by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : 2 * M ≤ N := Nat.mul_div_le N 2
      have : ((2 * M : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      push_cast at this; linarith)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lo : (1.41 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hL4 : L ≤ 1.3863 := by
    have : L = 2 * Real.log 2 := by
      simp only [L]; rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have hL0 : 0 ≤ L := Real.log_nonneg (by norm_num)
  have key : 8 / Real.sqrt 2 + Real.sqrt 2 * L ≤ 8 := by
    rw [div_add' _ _ _ hs2.ne', div_le_iff₀ hs2]
    nlinarith
  calc ∑ p ∈ Nat.primesLE M, Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) +
        ∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ M), Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ 8 * (Real.sqrt N / Real.sqrt 2) + Real.sqrt 2 * L * Real.sqrt N :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left hM2 (by norm_num))) hhigh
    _ = (8 / Real.sqrt 2 + Real.sqrt 2 * L) * Real.sqrt N := by ring
    _ ≤ 8 * Real.sqrt N := mul_le_mul_of_nonneg_right key hsN.le

/-- **`Σ_{p ≤ N} p^{−1/2} ≤ 2 N^{1/4} + 16 √N / log N`.** -/
theorem sum_primesLE_rpow_neg_half_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      2 * Real.sqrt (Real.sqrt N) + 16 * Real.sqrt N / Real.log N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE N) (fun p : ℕ => (p : ℝ) ≤ Real.sqrt N)]
  refine add_le_add ?_ ?_
  · -- small primes
    have hsub : (Nat.primesLE N).filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt N) ⊆
        Finset.Icc 1 ⌊Real.sqrt N⌋₊ := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.1.2.one_lt.le, Nat.le_floor hp.2⟩
    calc ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt N), (p : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.sqrt N⌋₊, (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
      _ = ∑ n ∈ Finset.Icc 1 ⌊Real.sqrt N⌋₊, (Real.sqrt n)⁻¹ :=
          Finset.sum_congr rfl fun n _ => natCast_rpow_neg_half_eq n
      _ ≤ 2 * Real.sqrt (⌊Real.sqrt N⌋₊ : ℝ) := Sieve.sum_sqrtInv_le _
      _ ≤ 2 * Real.sqrt (Real.sqrt N) := by
          gcongr; exact Nat.floor_le (Real.sqrt_nonneg _)
  · -- large primes carry a logarithm
    have hpt : ∀ p ∈ (Nat.primesLE N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt N),
        (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 / Real.log N * (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpN : Real.sqrt N < p := not_le.1 hp.2
      have hlogp : Real.log N / 2 < Real.log p := by
        rw [← Real.log_sqrt (by linarith)]
        exact Real.log_lt_log (Real.sqrt_pos.2 (by linarith)) hpN
      have hr : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
      have h1 : 1 ≤ 2 / Real.log N * Real.log p := by
        rw [div_mul_eq_mul_div, one_le_div hlogN]; linarith
      calc (p : ℝ) ^ (-(1 / 2 : ℝ)) = 1 * (p : ℝ) ^ (-(1 / 2 : ℝ)) := (one_mul _).symm
        _ ≤ 2 / Real.log N * Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h1 hr
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have hall : ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt N),
        Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 8 * Real.sqrt N :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ =>
        mul_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le))
          (Real.rpow_nonneg (Nat.cast_nonneg p) _)).trans (sum_primesLE_log_mul_rpow_neg_half_le N)
    calc 2 / Real.log N * ∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt N),
          Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ 2 / Real.log N * (8 * Real.sqrt N) := mul_le_mul_of_nonneg_left hall (by positivity)
      _ = 16 * Real.sqrt N / Real.log N := by ring

/-- The packet primes up to scale `X`: odd primes `q` with `2q ≤ X`. -/
def packetPrimes (X : ℕ) : Finset ℕ := (Nat.primesLE X).filter fun q => q ≠ 2 ∧ 2 * q ≤ X

/-- The half-power weight of the packets up to scale `X`. -/
def packetHalfWeight (X : ℕ) : ℝ :=
  ∑ q ∈ packetPrimes X, (((2 * q : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) + (packetPrime q : ℝ) ^ (-(1 / 2 : ℝ)))

/-- The squarefree count `#{n ≤ X : n squarefree}`. -/
def squarefreeCount (X : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 X, ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2

/-- The half-power weight `Σ_{n ≤ X} μ(n)²/√n` of the squarefree sites. -/
def squarefreeHalfWeight (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ (2 : ℕ) * (Real.sqrt n)⁻¹

theorem card_packetPrimes_le (X : ℕ) : (packetPrimes X).card ≤ X.primeCounting := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact Finset.card_filter_le _ _

/-- **`O(X/log X)` packets up to scale `X`.** -/
theorem isBigO_card_packetPrimes :
    (fun X : ℕ => ((packetPrimes X).card : ℝ)) =O[atTop] fun X : ℕ => (X : ℝ) / Real.log X := by
  refine IsBigO.of_bound (2 * Real.log 4 + 2) ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_le_log4_mul_div (x := (X : ℝ)) (by linarith)
  rw [Nat.floor_natCast, Real.log_sqrt (by linarith)] at hpi
  have hsq : Real.sqrt X ≤ 2 * X / Real.log X := by
    have h1 := Real.log_le_rpow_div (x := (X : ℝ)) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h1
    rw [le_div_iff₀ hlog]
    have h2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (X : ℝ)]
  have hcard : ((packetPrimes X).card : ℝ) ≤ X.primeCounting := by exact_mod_cast card_packetPrimes_le X
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (div_nonneg (by linarith) hlog.le)]
  calc ((packetPrimes X).card : ℝ) ≤ Real.log 4 * X / (Real.log X / 2) + Real.sqrt X := hcard.trans hpi
    _ ≤ Real.log 4 * X / (Real.log X / 2) + 2 * X / Real.log X := by linarith
    _ = (2 * Real.log 4 + 2) * (X / Real.log X) := by field_simp

/-- `|#{n ≤ X squarefree} − X/ζ(2)| ≤ 3√X` (with `ζ(2) = π²/6`). -/
theorem abs_squarefreeCount_sub_le {X : ℕ} (hX : 1 ≤ X) :
    |squarefreeCount X - X / (Real.pi ^ 2 / 6)| ≤ 3 * Real.sqrt X := by
  set R := Nat.sqrt X + 1
  have hR : 1 ≤ R := by omega
  have hRX : 0 + X ≤ R ^ 2 := by
    have := Nat.lt_succ_sqrt X
    rw [zero_add, sq]; exact this.le
  have h := Sieve.abs_window_squarefree_sub_le (t := 0) (L := X) hR hRX
  rw [zero_add, Sieve.squarefreeDensity_eq] at h
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hsX : 1 ≤ Real.sqrt X := Real.one_le_sqrt.2 hXR
  have hR1 : (R : ℝ) ≤ Real.sqrt X + 1 := by
    have := Real.nat_sqrt_le_real_sqrt (a := X); push_cast [R]; linarith
  have hR2 : Real.sqrt X ≤ R := by
    have := Real.real_sqrt_le_nat_sqrt_succ (a := X); push_cast [R]; linarith
  have hXdiv : (X : ℝ) / R ≤ Real.sqrt X := by
    rw [div_le_iff₀ (by positivity)]
    have : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
    nlinarith
  have heq : (X : ℝ) / (Real.pi ^ 2 / 6) = X * (6 / Real.pi ^ 2) := by
    field_simp
  rw [squarefreeCount, heq]
  linarith

/-- **`#{n ≤ X squarefree} = X/ζ(2) + o(X)`.** -/
theorem isLittleO_squarefreeCount :
    (fun X : ℕ => squarefreeCount X - X / (Real.pi ^ 2 / 6)) =o[atTop] fun X : ℕ => (X : ℝ) := by
  rw [isLittleO_iff]
  intro c hc
  have hlim : Tendsto (fun X : ℕ => Real.sqrt X) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_ge_atTop (3 / c)] with X hX hXc
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ X)]
  refine (abs_squarefreeCount_sub_le hX).trans ?_
  have hs : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
  have h3 : 3 ≤ c * Real.sqrt X := by rwa [div_le_iff₀' hc] at hXc
  nlinarith [Real.sqrt_nonneg (X : ℝ)]

theorem squarefreeHalfWeight_le (X : ℕ) : squarefreeHalfWeight X ≤ 2 * Real.sqrt X :=
  Sieve.sum_sqrtInv_squarefree_le X

theorem eventually_squarefreeHalfWeight_ge :
    ∀ᶠ X : ℕ in atTop, Real.sqrt X / 4 ≤ squarefreeHalfWeight X := by
  have hlim : Tendsto (fun X : ℕ => Real.sqrt X) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_ge_atTop 24] with X hX hX24
  set R := Nat.sqrt X + 1
  have hR : 1 ≤ R := by omega
  have hRX : X ≤ R ^ 2 := by
    have := Nat.lt_succ_sqrt X
    rw [sq]; exact this.le
  have h := Sieve.sum_sqrtInv_squarefree_ge hX hR hRX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hsX : 1 ≤ Real.sqrt X := Real.one_le_sqrt.2 hXR
  have hR1 : (R : ℝ) ≤ Real.sqrt X + 1 := by
    have := Real.nat_sqrt_le_real_sqrt (a := X); push_cast [R]; linarith
  have hR2 : Real.sqrt X ≤ R := by
    have := Real.real_sqrt_le_nat_sqrt_succ (a := X); push_cast [R]; linarith
  have hXdiv : (X : ℝ) / R ≤ Real.sqrt X := by
    rw [div_le_iff₀ (by positivity)]
    have : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
    nlinarith
  have herr : ((R : ℝ) + X / R) / Real.sqrt X ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hρ := Sieve.squarefreeDensity_ge
  rw [squarefreeHalfWeight]
  nlinarith

/-- **`O(√X/log X)` packet half-weight.** -/
theorem packetHalfWeight_le (X : ℕ) :
    packetHalfWeight X ≤ 2 * ∑ p ∈ Nat.primesLE X, (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [packetHalfWeight, Finset.mul_sum]
  refine (Finset.sum_le_sum fun q hq => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => by positivity)
  rw [packetPrimes, Finset.mem_filter, Nat.mem_primesLE] at hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1.2.pos
  have h1 : ((2 * q : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hq0 (by push_cast; linarith) (by norm_num)
  have h2 : (packetPrime q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hq0 (by exact_mod_cast (by have := two_mul_lt_packetPrime q; omega :
      q ≤ packetPrime q)) (by norm_num)
  linarith

/-- `log X ≤ √√X` eventually. -/
theorem eventually_log_le_sqrt_sqrt : ∀ᶠ X : ℕ in atTop, Real.log X ≤ Real.sqrt (Real.sqrt X) := by
  have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).bound one_pos
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with X hX hX1
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hXR
  have hq : Real.sqrt (Real.sqrt X) = (X : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]; norm_num
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hX
  rw [hq]; exact hX

/-- **The packet half-weight is `O(√X/log X)`.** -/
theorem isBigO_packetHalfWeight :
    (fun X : ℕ => packetHalfWeight X) =O[atTop] fun X : ℕ => Real.sqrt X / Real.log X := by
  refine IsBigO.of_bound 36 ?_
  filter_upwards [eventually_log_le_sqrt_sqrt, eventually_ge_atTop 2] with X hlogle hX2
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hW := (packetHalfWeight_le X).trans (mul_le_mul_of_nonneg_left (sum_primesLE_rpow_neg_half_le hX2)
    (by norm_num))
  have hW0 : 0 ≤ packetHalfWeight X := Finset.sum_nonneg fun q _ => by positivity
  set t := Real.sqrt X
  set u := Real.sqrt t
  have hss : u * u = t := Real.mul_self_sqrt hsX.le
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hut : u ≤ t / Real.log X := by
    rw [le_div_iff₀ hlog, ← hss]; nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hW0, abs_of_nonneg (by positivity)]
  calc packetHalfWeight X ≤ 2 * (2 * u + 16 * t / Real.log X) := hW
    _ ≤ 2 * (2 * (t / Real.log X) + 16 * t / Real.log X) := by gcongr
    _ = 36 * (t / Real.log X) := by ring

theorem tendsto_one_div_sqrt_sqrt :
    Tendsto (fun X : ℕ => 1 / Real.sqrt (Real.sqrt X)) atTop (𝓝 0) := by
  have h := (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  refine h.inv_tendsto_atTop.congr fun X => ?_
  simp only [Pi.inv_apply, Function.comp_apply, one_div]

theorem tendsto_one_div_log_nat : Tendsto (fun X : ℕ => 1 / Real.log X) atTop (𝓝 0) := by
  have h := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine h.inv_tendsto_atTop.congr fun X => ?_
  simp only [Pi.inv_apply, Function.comp_apply, one_div]

/-- **The packets cannot match the full source at half-power weight.**
`Σ_packets (m^{−1/2} + p^{−1/2}) / Σ_{n ≤ X} μ(n)²/√n → 0`. -/
theorem tendsto_packetHalfWeight_div_squarefreeHalfWeight :
    Tendsto (fun X : ℕ => packetHalfWeight X / squarefreeHalfWeight X) atTop (𝓝 0) := by
  have hlim := ((tendsto_one_div_sqrt_sqrt.const_mul 16).add (tendsto_one_div_log_nat.const_mul 128))
  rw [mul_zero, mul_zero, add_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_squarefreeHalfWeight_ge, eventually_ge_atTop 1] with X hX hX1
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
    have hpos : 0 < squarefreeHalfWeight X := lt_of_lt_of_le (by positivity) hX
    exact div_nonneg (Finset.sum_nonneg fun q _ => by positivity) hpos.le
  · filter_upwards [eventually_squarefreeHalfWeight_ge, eventually_ge_atTop 2] with X hX hX2
    have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX2
    have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
    have hssX : 0 < Real.sqrt (Real.sqrt X) := Real.sqrt_pos.2 hsX
    have hlog : 0 < Real.log X := Real.log_pos (by linarith)
    have hpos : 0 < squarefreeHalfWeight X := lt_of_lt_of_le (by positivity) hX
    have hW := (packetHalfWeight_le X).trans (mul_le_mul_of_nonneg_left (sum_primesLE_rpow_neg_half_le hX2)
      (by norm_num))
    have hW0 : 0 ≤ packetHalfWeight X := Finset.sum_nonneg fun q _ => by positivity
    set t := Real.sqrt X
    set u := Real.sqrt t
    have hss : u * u = t := Real.mul_self_sqrt hsX.le
    rw [div_le_iff₀ hpos]
    calc packetHalfWeight X ≤ 2 * (2 * u + 16 * t / Real.log X) := hW
      _ = (16 * (1 / u) + 128 * (1 / Real.log X)) * (t / 4) := by
          rw [← hss]; field_simp; ring
      _ ≤ (16 * (1 / Real.sqrt (Real.sqrt X)) + 128 * (1 / Real.log X)) * squarefreeHalfWeight X :=
          mul_le_mul_of_nonneg_left hX (by positivity)

/-- **Packet count against the squarefree count:** `#packets / #squarefree → 0`. -/
theorem tendsto_card_packetPrimes_div_squarefreeCount :
    Tendsto (fun X : ℕ => ((packetPrimes X).card : ℝ) / squarefreeCount X) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := isBigO_card_packetPrimes.bound
  have hlim := tendsto_one_div_log_nat.const_mul (4 * |C|)
  rw [mul_zero] at hlim
  have hsqrt : Tendsto (fun X : ℕ => Real.sqrt X) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hcount : ∀ᶠ X : ℕ in atTop, (X : ℝ) / 4 ≤ squarefreeCount X := by
    filter_upwards [eventually_ge_atTop 1, hsqrt.eventually_ge_atTop 24] with X hX hX24
    have h := abs_squarefreeCount_sub_le hX
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hs : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
    have hπ : (X : ℝ) / (Real.pi ^ 2 / 6) ≥ 3 / 8 * X := by
      have := Sieve.squarefreeDensity_ge
      rw [Sieve.squarefreeDensity_eq] at this
      rw [ge_iff_le, div_div_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    have := (abs_le.1 h).1
    nlinarith
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hcount, eventually_ge_atTop 1] with X hX hX1
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
    exact div_nonneg (Nat.cast_nonneg _) ((by positivity : (0 : ℝ) ≤ X / 4).trans hX)
  · filter_upwards [hcount, hC, eventually_ge_atTop 2] with X hX hCX hX2
    have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX2
    have hlog : 0 < Real.log X := Real.log_pos (by linarith)
    have hpos : 0 < squarefreeCount X := lt_of_lt_of_le (by positivity) hX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (div_nonneg (by linarith) hlog.le)] at hCX
    rw [div_le_iff₀ hpos]
    calc ((packetPrimes X).card : ℝ) ≤ C * (X / Real.log X) := hCX
      _ ≤ |C| * (X / Real.log X) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = 4 * |C| * (1 / Real.log X) * (X / 4) := by field_simp
      _ ≤ 4 * |C| * (1 / Real.log X) * squarefreeCount X :=
          mul_le_mul_of_nonneg_left hX (by positivity)

end

end RHTower
