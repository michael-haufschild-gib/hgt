import GaloisForLFunctions.HTGeometry.BuresWasserstein.WeightedGeometricMeanArith
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinEquation

/-!
# The Wasserstein mean dominates the inverse power mean

If the Wasserstein point `Ω` satisfies `Ω ≥ 1` then `X := Ω⁻¹` satisfies `X ≤ g_t(X)` for the
power-mean map `g_t` and every `t ∈ [1/2, 1]`: the affine parameter law rewrites
`X # Aᵢ = X #_{1/(2t)} (X #_t Aᵢ)`, the arithmetic–geometric mean inequality bounds it above by
`(1 - 1/(2t))X + (1/(2t))(X #_t Aᵢ)`, and summing with `∑ wᵢ = 1` and `X ≤ 1` gives
`X ≤ g_t(X)`.  Since `g_t` is monotone, `X ≤ g_t^r(X)` for all `r`, and the iterates converge to
the power mean; hence `Ω⁻¹ ≤ P_t`, that is `Ω ≥ P_t^{-1}`.
-/

open scoped NNReal Ring BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-- The power-mean map is monotone. -/
theorem powerMeanMap_mono {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) {X Y : A}
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y) (h : X ≤ Y) :
    powerMeanMap s w Av t X ≤ powerMeanMap s w Av t Y := by
  unfold powerMeanMap
  refine Finset.sum_le_sum fun i hi => ?_
  exact smul_le_smul_of_nonneg_left (wgm_mono_left ht hX hY (hA i hi) h) (hw i hi)

/-- **The power-mean iteration converges from any starting point of the interval.** -/
theorem tendsto_powerMeanMap_iterate [Nontrivial A] {t α β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A))
    {P : A} (hPα : α • (1 : A) ≤ P) (hPβ : P ≤ β • (1 : A))
    (hPfix : powerMeanMap s w Av t P = P)
    {X₀ : A} (hX₀α : α • (1 : A) ≤ X₀) (hX₀β : X₀ ≤ β • (1 : A)) :
    Tendsto (fun r => (powerMeanMap s w Av t)^[r] X₀) atTop (nhds P) := by
  have hPpos : IsStrictlyPositive P := isStrictlyPositive_of_smul_one_le hα hPα
  obtain ⟨Y, hYdef, hY0, hYsucc⟩ : ∃ f : ℕ → A,
      (∀ n, f n = (powerMeanMap s w Av t)^[n] X₀) ∧ f 0 = X₀
      ∧ ∀ n, f (n + 1) = powerMeanMap s w Av t (f n) :=
    ⟨fun n => (powerMeanMap s w Av t)^[n] X₀, fun _ => rfl, rfl, fun n => by
      show (powerMeanMap s w Av t)^[n + 1] X₀
        = powerMeanMap s w Av t ((powerMeanMap s w Av t)^[n] X₀)
      rw [Function.iterate_succ_apply']⟩
  have hYmem : ∀ n, IsStrictlyPositive (Y n) ∧ α • (1 : A) ≤ Y n ∧ Y n ≤ β • (1 : A) := by
    intro n
    induction n with
    | zero => exact ⟨isStrictlyPositive_of_smul_one_le hα (hY0 ▸ hX₀α), hY0 ▸ hX₀α, hY0 ▸ hX₀β⟩
    | succ n ih =>
        obtain ⟨hp, hlo, hhi⟩ := ih
        obtain ⟨h1, h2⟩ := powerMeanMap_mem_Icc (s := s) (w := w) (Av := Av)
          ⟨le_of_lt ht, ht1⟩ hα hβ hw hwsum hA hAα hAβ hp hlo hhi
        rw [hYsucc n]
        exact ⟨isStrictlyPositive_of_smul_one_le hα h1, h1, h2⟩
  obtain ⟨R, hRdef⟩ : ∃ f : ℕ → ℝ, f = fun n =>
      max (loewnerRatio (Y n) P) (loewnerRatio P (Y n)) := ⟨_, rfl⟩
  have hR1 : ∀ n, 1 ≤ R n := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hYmem n
    have hmul := one_le_loewnerRatio_mul hα hβ hp.nonneg hPpos.nonneg hlo hhi hPα hPβ
    have hp1 : 0 < loewnerRatio (Y n) P := loewnerRatio_pos hα hβ hPpos.nonneg hhi hPα hlo hPβ
    have hp2 : 0 < loewnerRatio P (Y n) := loewnerRatio_pos hα hβ hp.nonneg hPβ hlo hPα hhi
    rw [hRdef]
    by_contra hlt'
    have hlt : max (loewnerRatio (Y n) P) (loewnerRatio P (Y n)) < 1 := not_le.mp hlt'
    have h1 : loewnerRatio (Y n) P < 1 := lt_of_le_of_lt (le_max_left _ _) hlt
    have h2 : loewnerRatio P (Y n) < 1 := lt_of_le_of_lt (le_max_right _ _) hlt
    nlinarith [hmul, h1, h2, hp1, hp2]
  have hRdec : ∀ n, R (n + 1) - 1 ≤ (1 - t) * (R n - 1) := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hYmem n
    have hstep : ∀ U V : A, IsStrictlyPositive U → IsStrictlyPositive V →
        α • (1 : A) ≤ U → U ≤ β • (1 : A) → α • (1 : A) ≤ V → V ≤ β • (1 : A) →
        loewnerRatio U V ≤ R n →
        loewnerRatio (powerMeanMap s w Av t U) (powerMeanMap s w Av t V)
          ≤ 1 + (1 - t) * (R n - 1) := by
      intro U V hU hV hUα hUβ hVα hVβ hUV
      have hc := loewnerRatio_powerMeanMap_le (s := s) (w := w) (Av := Av) ht ht1 hα hβ
        hw hwsum hA hAα hAβ hU hV hUα hUβ hVα hVβ
      have hmono : (loewnerRatio U V) ^ (1 - t) ≤ (R n) ^ (1 - t) :=
        Real.rpow_le_rpow (loewnerRatio_nonneg U V) hUV (by linarith)
      have hbern : (R n) ^ (1 - t) ≤ 1 + (1 - t) * (R n - 1) :=
        rpow_le_one_add_mul_sub_one (by linarith [hR1 n]) (by linarith) (by linarith)
      linarith [hc, hmono, hbern]
    have e1 : loewnerRatio (Y (n + 1)) P ≤ 1 + (1 - t) * (R n - 1) := by
      have h := hstep (Y n) P hp hPpos hlo hhi hPα hPβ (by rw [hRdef]; exact le_max_left _ _)
      rwa [← hYsucc n, hPfix] at h
    have e2 : loewnerRatio P (Y (n + 1)) ≤ 1 + (1 - t) * (R n - 1) := by
      have h := hstep P (Y n) hPpos hp hPα hPβ hlo hhi (by rw [hRdef]; exact le_max_right _ _)
      rwa [← hYsucc n, hPfix] at h
    have hRn1 : R (n + 1) = max (loewnerRatio (Y (n + 1)) P) (loewnerRatio P (Y (n + 1))) := by
      rw [hRdef]
    have hmax : R (n + 1) ≤ 1 + (1 - t) * (R n - 1) := by
      rw [hRn1]
      exact max_le e1 e2
    linarith [hmax]
  have hRgeom : ∀ n, R n - 1 ≤ (1 - t) ^ n * (R 0 - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 := hRdec n
        have h2 : (1 - t) * (R n - 1) ≤ (1 - t) * ((1 - t) ^ n * (R 0 - 1)) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
        calc R (n + 1) - 1 ≤ (1 - t) * (R n - 1) := h1
          _ ≤ (1 - t) * ((1 - t) ^ n * (R 0 - 1)) := h2
          _ = (1 - t) ^ (n + 1) * (R 0 - 1) := by ring
  have hnorm : ∀ n, ‖Y n - P‖ ≤ (3 * β * (R 0 - 1)) * (1 - t) ^ n := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hYmem n
    have hb := norm_sub_le_of_loewnerRatio (a := Y n) (b := P) hα hβ hp.nonneg hPpos.nonneg
      hhi hPα hPβ hlo (hR1 n) (by rw [hRdef]; exact le_max_left _ _)
      (by rw [hRdef]; exact le_max_right _ _)
    refine hb.trans ?_
    have hg := hRgeom n
    have h3 := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 3 * β)
    have h4 : 3 * β * ((1 - t) ^ n * (R 0 - 1)) = 3 * β * (R 0 - 1) * (1 - t) ^ n := by ring
    linarith [h3, h4]
  have hconv : Tendsto (fun n => Y n) atTop (nhds P) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (?_ : Tendsto (fun n => (3 * β * (R 0 - 1)) * (1 - t) ^ n) atTop (nhds 0))
    · rw [dist_eq_norm]
      exact hnorm n
    · have hgeo : Tendsto (fun n : ℕ => (1 - t) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
      simpa using hgeo.const_mul (3 * β * (R 0 - 1))
  exact hconv.congr fun n => hYdef n

/-- The weighted geometric mean of strictly positive elements is strictly positive. -/
lemma wgm_strictlyPositive {t : ℝ} {X Y : A} (hX : IsStrictlyPositive X)
    (hY : IsStrictlyPositive Y) : IsStrictlyPositive (wgm t X Y) := by
  rw [wgm_def]
  exact IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _
    (hX.rpow X _).isUnit (isSelfAdjoint_rpow X _)
    ((conj_strictlyPositive hX hY).rpow _ t)

set_option maxHeartbeats 1000000 in
/-- **Theorem 6.8(i) (Kim–Mer–Pálfia).**  If the Wasserstein point dominates the identity then
it dominates the inverse of the power mean, for every parameter `t ∈ [1/2, 1]`. -/
theorem ringInverse_isWassersteinPoint_le_powerMean [Nontrivial A] {t γ δ : ℝ}
    (ht : 1/2 ≤ t) (ht1 : t ≤ 1) (hγ : 0 < γ) (hδ : 0 < δ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAγ : ∀ i ∈ s, γ • (1 : A) ≤ Av i) (hAδ : ∀ i ∈ s, Av i ≤ δ • (1 : A))
    {Om : A} (hOm : IsWassersteinPoint s w Av Om) (hOm1 : (1 : A) ≤ Om)
    (hXγ : γ • (1 : A) ≤ (Om⁻¹ʳ : A)) (hXδ : (Om⁻¹ʳ : A) ≤ δ • (1 : A))
    {P : A} (hPγ : γ • (1 : A) ≤ P) (hPδ : P ≤ δ • (1 : A))
    (hPfix : powerMeanMap s w Av t P = P) :
    (Om⁻¹ʳ : A) ≤ P := by
  have ht0 : 0 < t := by linarith
  have hX : IsStrictlyPositive (Om⁻¹ʳ : A) := hOm.1.ringInverse
  have hX1 : (Om⁻¹ʳ : A) ≤ 1 := by
    have h := ringInverse_le_of_smul_one_le (a := Om) (m := 1) one_pos (by rwa [one_smul])
    rwa [inv_one, one_smul] at h
  -- the Wasserstein equation, written with the inverse in the first slot
  have hsum : ∑ i ∈ s, w i • gm (Om⁻¹ʳ : A) (Av i) = 1 := by
    rw [← hOm.2]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gm_comm hX (hA i hi)]
  -- the affine parameter law and the arithmetic–geometric mean inequality
  obtain ⟨σ, hσdef⟩ : ∃ x : ℝ, x = 1 / (2 * t) := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  have hσ1 : σ ≤ 1 := by
    rw [hσdef, div_le_one (by linarith)]
    linarith
  have hkey : ∀ i ∈ s, gm (Om⁻¹ʳ : A) (Av i)
      ≤ (1 - σ) • (Om⁻¹ʳ : A) + σ • wgm t (Om⁻¹ʳ : A) (Av i) := by
    intro i hi
    have haff : wgm σ (Om⁻¹ʳ : A) (wgm t (Om⁻¹ʳ : A) (Av i)) = gm (Om⁻¹ʳ : A) (Av i) := by
      rw [wgm_wgm (ne_of_gt ht0) hX (hA i hi)]
      have hts : t * σ = 1 / 2 := by
        rw [hσdef]
        field_simp
      rw [hts]
      rfl
    rw [← haff]
    exact wgm_le_arith hσ0 hσ1 hX (wgm_strictlyPositive hX (hA i hi))
  -- summing gives `1 ≤ (1-σ) X + σ g(X)`
  have hsum2 : (1 : A)
      ≤ (1 - σ) • (Om⁻¹ʳ : A) + σ • powerMeanMap s w Av t (Om⁻¹ʳ : A) := by
    rw [← hsum]
    refine le_trans (Finset.sum_le_sum fun i hi =>
      smul_le_smul_of_nonneg_left (hkey i hi) (hw i hi)) (le_of_eq ?_)
    unfold powerMeanMap
    rw [Finset.smul_sum]
    have e1 : ∑ i ∈ s, w i • ((1 - σ) • (Om⁻¹ʳ : A) + σ • wgm t (Om⁻¹ʳ : A) (Av i))
        = (∑ i ∈ s, w i • ((1 - σ) • (Om⁻¹ʳ : A)))
          + ∑ i ∈ s, σ • (w i • wgm t (Om⁻¹ʳ : A) (Av i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      module
    rw [e1, ← Finset.sum_smul, hwsum, one_smul]
  -- hence `X ≤ g(X)`
  have hXg : (Om⁻¹ʳ : A) ≤ powerMeanMap s w Av t (Om⁻¹ʳ : A) := by
    have hσpos : 0 < σ := by rw [hσdef]; positivity
    have hscaled := smul_le_smul_of_nonneg_left hsum2 (le_of_lt (by positivity : (0:ℝ) < 2 * t))
    rw [smul_add, smul_smul, smul_smul] at hscaled
    have hc1 : (2 * t) * (1 - σ) = 2 * t - 1 := by
      rw [hσdef]
      field_simp
    have hc2 : (2 * t) * σ = 1 := by
      rw [hσdef]
      field_simp
    rw [hc1, hc2, one_smul] at hscaled
    have hstep : ((2 * t) : ℝ) • (Om⁻¹ʳ : A) ≤ (2 * t) • (1 : A) :=
      smul_le_smul_of_nonneg_left hX1 (by positivity)
    have hid : ((2 * t) : ℝ) • (Om⁻¹ʳ : A)
        = (2 * t - 1) • (Om⁻¹ʳ : A) + (Om⁻¹ʳ : A) := by
      rw [sub_smul, one_smul]
      abel
    rw [hid] at hstep
    have hfin : (2 * t - 1) • (Om⁻¹ʳ : A) + (Om⁻¹ʳ : A)
        ≤ (2 * t - 1) • (Om⁻¹ʳ : A) + powerMeanMap s w Av t (Om⁻¹ʳ : A) :=
      le_trans hstep hscaled
    exact le_of_add_le_add_left hfin
  -- the iterates stay in the interval and dominate `X`
  have hmem : ∀ r : ℕ, IsStrictlyPositive ((powerMeanMap s w Av t)^[r] (Om⁻¹ʳ : A))
      ∧ γ • (1 : A) ≤ (powerMeanMap s w Av t)^[r] (Om⁻¹ʳ : A)
      ∧ (powerMeanMap s w Av t)^[r] (Om⁻¹ʳ : A) ≤ δ • (1 : A) := by
    intro r
    induction r with
    | zero => exact ⟨hX, hXγ, hXδ⟩
    | succ r ih =>
        obtain ⟨hp, hlo, hhi⟩ := ih
        obtain ⟨h1, h2⟩ := powerMeanMap_mem_Icc (s := s) (w := w) (Av := Av)
          ⟨le_of_lt ht0, ht1⟩ hγ hδ hw hwsum hA hAγ hAδ hp hlo hhi
        rw [Function.iterate_succ_apply']
        exact ⟨isStrictlyPositive_of_smul_one_le hγ h1, h1, h2⟩
  have hdom : ∀ r : ℕ, (Om⁻¹ʳ : A) ≤ (powerMeanMap s w Av t)^[r] (Om⁻¹ʳ : A) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Function.iterate_succ_apply']
        refine le_trans hXg ?_
        exact powerMeanMap_mono ⟨le_of_lt ht0, ht1⟩ hw hA hX (hmem r).1 ih
  -- pass to the limit
  have hconv := tendsto_powerMeanMap_iterate (s := s) (w := w) (Av := Av) ht0 ht1 hγ hδ
    hw hwsum hA hAγ hAδ hPγ hPδ hPfix hXγ hXδ
  have hcl : IsClosed {y : A | (Om⁻¹ʳ : A) ≤ y} := by
    have hset : {y : A | (Om⁻¹ʳ : A) ≤ y}
        = (fun y : A => y - (Om⁻¹ʳ : A)) ⁻¹' {z : A | 0 ≤ z} := by
      ext y
      simp [sub_nonneg]
    rw [hset]
    exact IsClosed.preimage (by fun_prop) CStarAlgebra.isClosed_nonneg
  exact hcl.mem_of_tendsto hconv (Eventually.of_forall fun r => hdom r)

/-- **Theorem 6.8(i), in the paper's form**: `Ω ≥ P_t^{-1}`.  Part (ii) of the theorem is the
same statement, since `P_t(ω; 𝔸⁻¹)` is *defined* as `P_{−t}(ω; 𝔸)^{-1}` for negative `t`. -/
theorem powerMean_ringInverse_le_isWassersteinPoint [Nontrivial A] {t γ δ : ℝ}
    (ht : 1/2 ≤ t) (ht1 : t ≤ 1) (hγ : 0 < γ) (hδ : 0 < δ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAγ : ∀ i ∈ s, γ • (1 : A) ≤ Av i) (hAδ : ∀ i ∈ s, Av i ≤ δ • (1 : A))
    {Om : A} (hOm : IsWassersteinPoint s w Av Om) (hOm1 : (1 : A) ≤ Om)
    (hXγ : γ • (1 : A) ≤ (Om⁻¹ʳ : A)) (hXδ : (Om⁻¹ʳ : A) ≤ δ • (1 : A))
    {P : A} (_hPpos : IsStrictlyPositive P)
    (hPγ : γ • (1 : A) ≤ P) (hPδ : P ≤ δ • (1 : A))
    (hPfix : powerMeanMap s w Av t P = P) :
    (P⁻¹ʳ : A) ≤ Om := by
  have hle := ringInverse_isWassersteinPoint_le_powerMean (s := s) (w := w) (Av := Av)
    ht ht1 hγ hδ hw hwsum hA hAγ hAδ hOm hOm1 hXγ hXδ hPγ hPδ hPfix
  have hinv := CStarAlgebra.ringInverse_le_ringInverse hle hOm.1.ringInverse
  rwa [Ring.inverse_inverse hOm.1.isUnit] at hinv

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
