import GaloisForLFunctions.RHTower.WeilWorkExposingRayMassMargin
import GaloisForLFunctions.RHTower.DigammaDifferenceSeries
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum

/-!
# Positive gamma remainder and the adaptive truncation boundary

Two fixed samples of the literal exposing ray force a positive bounded
frequency moment for every exact matched nonnegative family. The quarter-line
digamma series then forces an inverse-square omitted-mode energy floor.
On one exact near-threshold family, every row-dependent bare truncation below
the exponential half-rate misses the exposing threshold.

The signed constant term is retained. These results do not prove a sign for
the complete energy and do not exclude analytic lower remainder corrections.
The mode count is not a real-frequency cutoff or a Galerkin dimension.
Paper proof: docs/reports/weil-work/results/02-exposing-ray/GAMMA-TRUNCATION-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Zeta23
noncomputable section
namespace RHTower.ExposingRayGamma

/-- A nonnegative term in the literal quarter-line digamma expansion. -/
def mode (j : ℕ) (τ : ℝ) : ℝ :=
  τ^2/((1/4+(j:ℝ))*(4*(1/4+(j:ℝ))^2+τ^2))

/-- The signed constant term is retained in every finite approximation. -/
def symbol (K : ℕ) (τ : ℝ) : ℝ :=
  archimedeanWeilSymbol 0 + ∑ j ∈ Finset.range K, mode j τ

def energy (K : ℕ) (f : ℝ → ℂ) : ℝ :=
  ∫ τ : ℝ, ‖paperFT f τ‖^2 * symbol K τ

/-- A bounded frequency moment that vanishes only at zero frequency. -/
def moment (f : ℝ → ℂ) : ℝ :=
  ∫ τ : ℝ, ‖paperFT f τ‖^2 * (τ^2/(1+τ^2))

theorem mode_nonneg (j : ℕ) (τ : ℝ) : 0 ≤ mode j τ := by
  unfold mode
  positivity

theorem mode_le (j : ℕ) (τ : ℝ) : mode j τ ≤ 4 := by
  have ha : 0 < (1:ℝ)/4+j := by positivity
  have hb : 0 < 4*((1:ℝ)/4+j)^2+τ^2 := by positivity
  unfold mode
  apply (div_le_iff₀ (mul_pos ha hb)).mpr
  have hc : (1:ℝ) ≤ 4*(1/4+j) := by linarith [Nat.cast_nonneg (α := ℝ) j]
  nlinarith only [sq_nonneg τ, sq_nonneg ((1:ℝ)/4+j),
    mul_le_mul_of_nonneg_right hc (sq_nonneg τ),
    mul_nonneg ha.le (sq_nonneg ((1:ℝ)/4+j))]

theorem hasSum_mode (τ : ℝ) :
    HasSum (fun j : ℕ => mode j τ)
      (archimedeanWeilSymbol (τ/(2*π))-archimedeanWeilSymbol 0) := by
  let a : ℂ := ((1/4:ℝ):ℂ)
  let b : ℂ := ((1/4:ℝ):ℂ)+((τ/2:ℝ):ℂ)*Complex.I
  have ha : 0 < a.re := by dsimp [a]; norm_num
  have hb : 0 < b.re := by dsimp [b]; simp [Complex.mul_re]
  have hsum := Complex.hasSum_re (hasSum_digamma_sub ha hb)
  have ht (j : ℕ) : mode j τ = (1/(a+j)-1/(b+j)).re := by
    dsimp only [a,b]
    have hz : (1/(((1/4:ℝ):ℂ)+(j:ℂ))).re = 1/((1:ℝ)/4+j) := by
      calc
        _ = ((1:ℝ)/4+j)/(((1:ℝ)/4+j)^2+0^2) := by
          simpa using re_one_div_vertical (1/4) 0 j
        _ = _ := by rw [zero_pow (by norm_num),add_zero,pow_two]; simp [one_div]
    rw [Complex.sub_re,hz,re_one_div_vertical]
    have hj : (1:ℝ)/4+j ≠ 0 := by positivity
    have hd : ((1:ℝ)/4+j)^2+(τ/2)^2 ≠ 0 := by positivity
    have he : 4*((1:ℝ)/4+j)^2+τ^2 ≠ 0 := by positivity
    unfold mode
    field_simp
    ring
  have hr : archimedeanWeilSymbol (τ/(2*π))-archimedeanWeilSymbol 0 =
      (Complex.digamma b-Complex.digamma a).re := by
    rw [archimedeanWeilSymbol_eq,archimedeanWeilSymbol_eq]
    have hp : π*(τ/(2*π))=τ/2 := by field_simp
    simp only [hp,mul_zero,Complex.ofReal_zero,zero_mul,add_zero,Complex.sub_re]
    dsimp [a,b]
    ring
  rw [hr]
  simpa only [← ht] using hsum

theorem symbol_remainder_lower {K : ℕ} (hK : 1 ≤ K) (τ : ℝ) :
    (τ^2/(1+τ^2))/(32*(K:ℝ)^2) ≤
      archimedeanWeilSymbol (τ/(2*π))-symbol K τ := by
  have hKpos : 0 < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKone : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hs := sum_le_hasSum (Finset.range (K+K))
    (fun j _ => mode_nonneg j τ) (hasSum_mode τ)
  rw [Finset.sum_range_add] at hs
  have hj : ∀ j ∈ Finset.range K,
      τ^2/(2*K*(16*(K:ℝ)^2+τ^2)) ≤ mode (K+j) τ := by
    intro j hj
    have hjK : (j:ℝ)+1 ≤ K := by exact_mod_cast (Finset.mem_range.mp hj)
    have ha : 0 < (1:ℝ)/4+(K+j) := by positivity
    have haK : (1:ℝ)/4+(K+j) ≤ 2*K := by linarith
    have hsq : ((1:ℝ)/4+(K+j))^2 ≤ 4*(K:ℝ)^2 := by nlinarith
    unfold mode
    push_cast
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact mul_le_mul haK (by linarith) (by positivity) (by positivity)
  have hh := Finset.sum_le_sum hj
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have he : (K:ℝ)*(τ^2/(2*K*(16*(K:ℝ)^2+τ^2))) =
      τ^2/(2*(16*(K:ℝ)^2+τ^2)) := by field_simp
  rw [he] at hh
  have hb : (τ^2/(1+τ^2))/(32*(K:ℝ)^2) ≤
      τ^2/(2*(16*(K:ℝ)^2+τ^2)) := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have hKK : (1:ℝ) ≤ (K:ℝ)^2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hKK (sq_nonneg τ)]
  dsimp [symbol]
  linarith

private theorem density_integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a)
    {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ τ, |g τ| ≤ B) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2*g τ) := by
  have hi := integrable_normSq_paperFT hf hs
  apply (hi.const_mul B).mono' (hi.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [] with τ
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hB τ) (sq_nonneg ‖paperFT f τ‖)

private theorem continuous_mode (j : ℕ) : Continuous (mode j) := by
  unfold mode
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro τ
  positivity

private theorem integrable_symbol {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) (K : ℕ) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2*symbol K τ) := by
  have hg : Continuous (symbol K) := by
    unfold symbol
    apply continuous_const.add
    exact continuous_finsetSum _ fun j _ => continuous_mode j
  apply density_integrable hf hs hg (B := |archimedeanWeilSymbol 0|+4*K)
  intro τ
  have hnon : 0 ≤ ∑ j ∈ Finset.range K, mode j τ :=
    Finset.sum_nonneg fun j _ => mode_nonneg j τ
  have hsum : (∑ j ∈ Finset.range K, mode j τ) ≤ 4*K := by
    calc _ ≤ ∑ _j ∈ Finset.range K, (4:ℝ) := Finset.sum_le_sum fun j _ => mode_le j τ
      _ = _ := by simp [mul_comm]
  exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hnon]; linarith)

private theorem integrable_moment {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2*(τ^2/(1+τ^2))) := by
  apply density_integrable hf hs (B := 1)
  · apply Continuous.div (by fun_prop) (by fun_prop)
    intro τ
    positivity
  · intro τ
    rw [abs_of_nonneg (by positivity),div_le_iff₀ (by positivity)]
    linarith

theorem moment_nonneg (f : ℝ → ℂ) : 0 ≤ moment f :=
  integral_nonneg fun τ => by positivity

/-- The omitted gamma modes pay a bounded frequency moment for every compact C² source. -/
theorem energy_remainder_lower {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) {K : ℕ} (hK : 1 ≤ K) :
    moment f/(32*(K:ℝ)^2) ≤ archEnergy f-energy K f := by
  have hiE := integrable_normSq_paperFT_mul_arch hf hs
  have hiK := integrable_symbol hf hs K
  have hiR := integrable_moment hf hs
  have h := integral_mono (hiR.div_const (32*(K:ℝ)^2)) (hiE.sub hiK) fun τ => by
    dsimp only [Pi.sub_apply]
    have hh := mul_le_mul_of_nonneg_left (symbol_remainder_lower hK τ)
      (sq_nonneg ‖paperFT f τ‖)
    simpa only [mul_sub,mul_div_assoc] using hh
  simp only [Pi.sub_apply] at h
  rw [integral_div,integral_sub hiE hiK] at h
  exact h

private theorem cosine_difference_le (τ u v : ℝ) :
    cos (τ*u)-cos (τ*v) ≤ (4+u^2+v^2)*(τ^2/(1+τ^2)) := by
  rw [← mul_div_assoc]
  have hden : 0 < 1+τ^2 := by positivity
  by_cases ht : τ^2 ≤ 1
  · have hh : cos (τ*u)-cos (τ*v) ≤ (u^2+v^2)*τ^2/2 := by
      nlinarith [cos_le_one (τ*u),one_sub_sq_div_two_le_cos (x := τ*v),sq_nonneg (τ*u)]
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left (show 1+τ^2 ≤ 2 by linarith)
      (show 0 ≤ (u^2+v^2)*τ^2/2 by positivity)
    nlinarith only [h,sq_nonneg τ]
  · have hh : cos (τ*u)-cos (τ*v) ≤ 2 := by
      linarith [cos_le_one (τ*u),neg_one_le_cos (τ*v)]
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg τ),
      mul_nonneg (sq_nonneg v) (sq_nonneg τ)]

/-- Two logarithmic traces control an actual bounded spectral moment. -/
theorem atom_difference_le {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) (p q : ℕ) :
    π*(atomCoeff f p-atomCoeff f q) ≤ (4+(log p)^2+(log q)^2)*moment f := by
  have hiP := integrable_normSq_paperFT_mul_cos hf hs (log p)
  have hiQ := integrable_normSq_paperFT_mul_cos hf hs (log q)
  have hiR := integrable_moment hf hs
  have h := integral_mono (hiP.sub hiQ) (hiR.const_mul (4+(log p)^2+(log q)^2)) fun τ => by
    dsimp only [Pi.sub_apply]
    have hh := mul_le_mul_of_nonneg_left (cosine_difference_le τ (log p) (log q))
      (sq_nonneg ‖paperFT f τ‖)
    nlinarith only [hh]
  simp only [Pi.sub_apply] at h
  rw [integral_sub hiP hiQ,integral_const_mul,
    integral_normSq_paperFT_mul_cos_eq hf hs,
    integral_normSq_paperFT_mul_cos_eq hf hs] at h
  dsimp only [atomCoeff,moment]
  linarith only [h]

private theorem exponential_nat_zero {r : ℝ} (hr : 0 < r) (C : ℝ) :
    Tendsto (fun N : ℕ => C*exp (-(r*N))) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he := tendsto_exp_atBot.comp
    (Filter.Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hr) hn)
  simpa only [Function.comp_apply,neg_mul,mul_zero] using he.const_mul C

private theorem two_fixed_samples :
    ∃ p q : ℕ, 2 ≤ p ∧ p ≤ q ∧ 0 < exposingWeight p-exposingWeight q := by
  obtain ⟨p,hp,hwp⟩ := ((eventually_ge_atTop 2).and exposingWeight_eventually_pos).exists
  have hr : 0 < exposingWeightDecayRate/2 := div_pos exposingWeightDecayRate_pos (by norm_num)
  obtain ⟨C,hC,hupper⟩ := exposingWeight_exponential_upper hr (by
    linarith [exposingWeightDecayRate_pos])
  have ht := (exponential_nat_zero hr C).eventually_lt_const
    (show 0 < exposingWeight p/2 by positivity)
  obtain ⟨q,hq,hsmall⟩ := ((eventually_ge_atTop p).and ht).exists
  have hbound := (le_abs_self (exposingWeight q)).trans (hupper q (by omega))
  exact ⟨p,q,hp,hq,by linarith⟩

/-- Exact ray matching forces bounded spectral mass away from zero. The constants
depend on two fixed ray samples, not on aperture, row count, or representation. -/
theorem matched_moment_floor :
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {ι : Type} [Fintype ι] (a : ι → ℝ) (f : ι → ℝ → ℂ) (α : ι → ℝ) (t : ℝ),
        (∀ i, IsPolarTest (a i) (f i)) → (∀ i, 0 ≤ α i) →
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=t*exposingWeightTrunc N n) →
        32*d*t ≤ ∑ i, α i*moment (f i) := by
  obtain ⟨p,q,hp,hpq,hΔ⟩ := two_fixed_samples
  let C := 4+(log p)^2+(log q)^2
  have hC : 0 < C := by dsimp [C]; positivity
  let d := (exposingWeight p-exposingWeight q)/(64*C)
  have hd : 0 < d := div_pos hΔ (by positivity)
  refine ⟨d,hd,q,fun N hN => ?_⟩
  intro ι _ a f α t hf hα hm
  have hP := hm p hp
  have hQ := hm q (by omega)
  rw [exposingWeightTrunc,if_pos (hpq.trans hN)] at hP
  rw [exposingWeightTrunc,if_pos hN] at hQ
  have hb : π*((∑ i, α i*atomCoeff (f i) p)-(∑ i, α i*atomCoeff (f i) q)) ≤
      C*∑ i, α i*moment (f i) := by
    calc _ = ∑ i, α i*(π*(atomCoeff (f i) p-atomCoeff (f i) q)) := by
           rw [← Finset.sum_sub_distrib,Finset.mul_sum]
           congr 1
           ext i
           ring
      _ ≤ ∑ i, α i*(C*moment (f i)) := by
           apply Finset.sum_le_sum
           intro i _
           exact mul_le_mul_of_nonneg_left
             (atom_difference_le (hf i).2.1 (hf i).2.2.1 p q) (hα i)
      _ = _ := by rw [Finset.mul_sum]; congr 1; ext i; ring
  have hdC : 32*d*t*C=t*(exposingWeight p-exposingWeight q)/2 := by
    dsimp [d]
    field_simp
    ring
  apply (mul_le_mul_iff_left₀ hC).mp
  nlinarith only [hb,hP,hQ,hdC]

/-- Every exact matched family pays the inverse-square omitted-mode floor. -/
theorem matched_remainder_floor :
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {ι : Type} [Fintype ι] (a : ι → ℝ) (f : ι → ℝ → ℂ) (α : ι → ℝ) (t : ℝ),
        (∀ i, IsPolarTest (a i) (f i)) → (∀ i, 0 ≤ α i) →
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=t*exposingWeightTrunc N n) →
        ∀ K : ℕ, 1 ≤ K → d*t/(K:ℝ)^2 ≤
          ∑ i, α i*(archEnergy (f i)-energy K (f i)) := by
  obtain ⟨d,hd,N₀,hfloor⟩ := matched_moment_floor
  refine ⟨d,hd,N₀,fun N hN => ?_⟩
  intro ι _ a f α t hf hα hm K hK
  have hR := hfloor N hN a f α t hf hα hm
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (energy_remainder_lower (hf i).2.1 (hf i).2.2.1 hK) (hα i)
  simp only [← mul_div_assoc,← Finset.sum_div] at hsum
  have hb := div_le_div_of_nonneg_right hR (show 0 ≤ 32*(K:ℝ)^2 by positivity)
  have he : 32*d*t/(32*(K:ℝ)^2)=d*t/(K:ℝ)^2 := by ring
  rw [he] at hb
  exact hb.trans hsum

private theorem row_adaptive_remainder {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a)
    {K : ℕ} (hK : 1 ≤ K) {x : ℝ} (hcap : (K:ℝ) ≤ exp x) :
    exp (-(2*x))/32*moment f ≤ archEnergy f-energy K f := by
  have hKpos : 0 < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hsq : (K:ℝ)^2 ≤ (exp x)^2 := by nlinarith [exp_pos x]
  have he : exp (-(2*x))*(K:ℝ)^2 ≤ 1 := by
    calc _ ≤ exp (-(2*x))*(exp x)^2 :=
        mul_le_mul_of_nonneg_left hsq (exp_pos _).le
      _ = 1 := by
        rw [pow_two,← mul_assoc,← exp_add,← exp_add]
        rw [show -(2*x)+x+x=0 by ring,exp_zero]
  apply le_trans ?_ (energy_remainder_lower hf hs hK)
  apply (le_div_iff₀ (show 0 < 32*(K:ℝ)^2 by positivity)).mpr
  have h := mul_le_mul_of_nonneg_right he (moment_nonneg f)
  nlinarith only [h]

/-- One exact matched family defeats every row-dependent bare truncation below
the exponential half-rate. The family is chosen before the mode counts. -/
theorem adaptive_truncation_counterexample :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < exposingWeightDecayRate/2 →
      ∀ᶠ N : ℕ in atTop, N ≤ ⌊exp (2*(log N/2+C))⌋₊ ∧
      ∃ (m : ℕ) (a : Fin m → ℝ) (f : Fin m → ℝ → ℂ) (α : Fin m → ℝ),
        (∀ i, a i ≤ log N/2+C) ∧ (∀ i, IsPolarTest (a i) (f i)) ∧
        (∀ i, 0 ≤ α i) ∧
        (∀ n : ℕ, 2 ≤ n → 2*π*∑ i, α i*atomCoeff (f i) n=exposingWeightTrunc N n) ∧
        ∀ K : Fin m → ℕ, (∀ i, 1 ≤ K i) → (∀ i, (K i:ℝ) ≤ exp (r*N)) →
          (∑ i, α i*energy (K i) (f i)) < archimedeanExposingThreshold-exposingTail N := by
  obtain ⟨C,m₀,hC,hm₀,hfam⟩ := ExposingRayMass.near_threshold_mass
  obtain ⟨d,hd,N₀,hfloor⟩ := matched_moment_floor
  refine ⟨C,hC,fun r hr hrate => ?_⟩
  let s := (2*r+exposingWeightDecayRate)/2
  have hspos : 0 < s := by dsimp [s]; linarith [exposingWeightDecayRate_pos]
  have hsrate : s < exposingWeightDecayRate := by dsimp [s]; linarith
  have hsr : 0 < s-2*r := by dsimp [s]; linarith
  obtain ⟨B,hB,hT⟩ := exposingTail_exponential_upper hspos hsrate
  have hsmall := (exponential_nat_zero hsr (3*B)).eventually_lt_const hd
  filter_upwards [hfam,hsmall,eventually_ge_atTop N₀,eventually_ge_atTop 1]
    with N hN hsmall hNN hN1
  obtain ⟨m,a,f,α,ha,hf,hα,hm,hM,hE⟩ := hN
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlevel : N ≤ ⌊exp (2*(log N/2+C))⌋₊ := by
    apply Nat.le_floor
    calc (N:ℝ) = exp (log N) := (exp_log hNpos).symm
      _ ≤ exp (2*(log N/2+C)) := exp_le_exp.mpr (by linarith)
  have hR := hfloor N hNN a f α 1 hf hα (by simpa only [one_mul] using hm)
  simp only [mul_one] at hR
  have htail : 3*exposingTail N < d*exp (-(2*(r*N))) := by
    calc _ ≤ 3*(B*exp (-(s*N))) := mul_le_mul_of_nonneg_left (hT N) (by norm_num)
      _ = (3*B*exp (-((s-2*r)*N)))*exp (-(2*(r*N))) := by
        rw [show -(s*(N:ℝ)) = -((s-2*r)*N)+-(2*(r*N)) by ring,exp_add]
        ring
      _ < _ := mul_lt_mul_of_pos_right hsmall (exp_pos _)
  refine ⟨hlevel,m,a,f,α,ha,hf,hα,hm,fun K hK hcap => ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left
      (row_adaptive_remainder (hf i).2.1 (hf i).2.2.1 (hK i) (hcap i)) (hα i)
  have hid : (∑ i, α i*(exp (-(2*(r*N)))/32*moment (f i))) =
      exp (-(2*(r*N)))/32*(∑ i, α i*moment (f i)) := by
    rw [Finset.mul_sum]
    congr 1
    ext i
    ring
  simp_rw [mul_sub] at hsum
  rw [hid,Finset.sum_sub_distrib] at hsum
  have hgap := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ exp (-(2*(r*N)))/32 by positivity)
  nlinarith only [hgap,hsum,htail,hE]

end RHTower.ExposingRayGamma
