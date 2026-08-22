import GaloisForLFunctions.HTGeometry.BuresWasserstein.PowerMeanContraction

/-!
# The Lim–Pálfia power mean

The power mean `P_t(ω; 𝔸)` of parameter `t ∈ (0,1]` is the unique strictly positive solution of

`X = ∑ᵢ wᵢ (X #_t Aᵢ)`.

Uniqueness is immediate from the Loewner-ratio contraction: two fixed points satisfy
`M(X/Y) ≤ M(X/Y)^{1-t}`, forcing `M(X/Y) ≤ 1`, and symmetrically.  Existence follows by
iterating the map from `α·1`: the Loewner ratio of consecutive iterates decays geometrically —
`M - 1 ≤ (1-t)^n (M₀ - 1)` by the weighted AM–GM inequality `x^s ≤ 1 + s(x-1)` — so the
increments are summable in norm and the sequence converges.
-/

open scoped NNReal Ring BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-- **Bernoulli from the weighted AM–GM inequality**: `x^s ≤ 1 + s(x-1)` for `0 ≤ s ≤ 1`. -/
theorem rpow_le_one_add_mul_sub_one {x σ : ℝ} (hx : 0 ≤ x) (hs0 : 0 ≤ σ) (hs1 : σ ≤ 1) :
    x ^ σ ≤ 1 + σ * (x - 1) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hs0 (by linarith : (0:ℝ) ≤ 1 - σ) hx
    zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at h
  linarith

/-- Uniqueness of the power mean. -/
theorem powerMeanMap_fixedPoint_unique [Nontrivial A] {t α β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A))
    {X Y : A} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hYα : α • (1 : A) ≤ Y) (hYβ : Y ≤ β • (1 : A))
    (hFX : powerMeanMap s w Av t X = X) (hFY : powerMeanMap s w Av t Y = Y) :
    X = Y := by
  have key : ∀ U V : A, IsStrictlyPositive U → IsStrictlyPositive V →
      α • (1 : A) ≤ U → U ≤ β • (1 : A) → α • (1 : A) ≤ V → V ≤ β • (1 : A) →
      powerMeanMap s w Av t U = U → powerMeanMap s w Av t V = V → U ≤ V := by
    intro U V hU hV hUα hUβ hVα hVβ hFU hFV
    have hc := loewnerRatio_powerMeanMap_le (s := s) (w := w) (Av := Av) ht ht1 hα hβ
      hw hwsum hA hAα hAβ hU hV hUα hUβ hVα hVβ
    rw [hFU, hFV] at hc
    have hpos : 0 < loewnerRatio U V := loewnerRatio_pos hα hβ hV.nonneg hUβ hVα hUα hVβ
    have hle1 : loewnerRatio U V ≤ 1 := by
      by_contra hgt
      have hgt' : 1 < loewnerRatio U V := not_le.mp hgt
      have hlt : (loewnerRatio U V) ^ (1 - t) < (loewnerRatio U V) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hgt' (by linarith)
      rw [Real.rpow_one] at hlt
      linarith [hc, hlt]
    have hM := le_loewnerRatio_smul hα hβ hV.nonneg hUβ hVα
    refine hM.trans ?_
    have h1 : loewnerRatio U V • V ≤ (1 : ℝ) • V :=
      smul_le_smul_of_nonneg_right hle1 hV.nonneg
    rwa [one_smul] at h1
  exact le_antisymm (key X Y hX hY hXα hXβ hYα hYβ hFX hFY)
    (key Y X hY hX hYα hYβ hXα hXβ hFY hFX)

/-- The power-mean map is Lipschitz in the operator norm on a Loewner interval. -/
theorem norm_powerMeanMap_sub_le [Nontrivial A] {t α β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A))
    {X Y : A} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A))
    (hYα : α • (1 : A) ≤ Y) (hYβ : Y ≤ β • (1 : A)) :
    ‖powerMeanMap s w Av t X - powerMeanMap s w Av t Y‖
      ≤ (3 * β * ((1 - t) / α)) * ‖X - Y‖ := by
  obtain ⟨hFXα, hFXβ⟩ := powerMeanMap_mem_Icc (s := s) (w := w) (Av := Av)
    ⟨le_of_lt ht, ht1⟩ hα hβ hw hwsum hA hAα hAβ hX hXα hXβ
  obtain ⟨hFYα, hFYβ⟩ := powerMeanMap_mem_Icc (s := s) (w := w) (Av := Av)
    ⟨le_of_lt ht, ht1⟩ hα hβ hw hwsum hA hAα hAβ hY hYα hYβ
  have hFX : IsStrictlyPositive (powerMeanMap s w Av t X) :=
    isStrictlyPositive_of_smul_one_le hα hFXα
  have hFY : IsStrictlyPositive (powerMeanMap s w Av t Y) :=
    isStrictlyPositive_of_smul_one_le hα hFYα
  have hsym : ‖Y - X‖ = ‖X - Y‖ := by rw [← norm_neg (X - Y), neg_sub]
  have hbound : ∀ U V : A, IsStrictlyPositive U → IsStrictlyPositive V →
      α • (1 : A) ≤ U → U ≤ β • (1 : A) → α • (1 : A) ≤ V → V ≤ β • (1 : A) →
      loewnerRatio (powerMeanMap s w Av t U) (powerMeanMap s w Av t V)
        ≤ 1 + (1 - t) * (‖U - V‖ / α) := by
    intro U V hU hV hUα hUβ hVα hVβ
    have hc := loewnerRatio_powerMeanMap_le (s := s) (w := w) (Av := Av) ht ht1 hα hβ
      hw hwsum hA hAα hAβ hU hV hUα hUβ hVα hVβ
    have hr : loewnerRatio U V ≤ 1 + ‖U - V‖ / α :=
      loewnerRatio_le_one_add hα (hU.isSelfAdjoint.sub hV.isSelfAdjoint) hVα
    have hmono : (loewnerRatio U V) ^ (1 - t) ≤ (1 + ‖U - V‖ / α) ^ (1 - t) :=
      Real.rpow_le_rpow (loewnerRatio_nonneg U V) hr (by linarith)
    have hbern : (1 + ‖U - V‖ / α) ^ (1 - t) ≤ 1 + (1 - t) * ((1 + ‖U - V‖ / α) - 1) :=
      rpow_le_one_add_mul_sub_one (by positivity) (by linarith) (by linarith)
    have hsimp : (1 + ‖U - V‖ / α) - 1 = ‖U - V‖ / α := by ring
    rw [hsimp] at hbern
    linarith [hc, hmono, hbern]
  have h1 := hbound X Y hX hY hXα hXβ hYα hYβ
  have h2 := hbound Y X hY hX hYα hYβ hXα hXβ
  rw [hsym] at h2
  have hρ1 : (1 : ℝ) ≤ 1 + (1 - t) * (‖X - Y‖ / α) := by
    have : (0 : ℝ) ≤ (1 - t) * (‖X - Y‖ / α) := by positivity
    linarith
  have hfin := norm_sub_le_of_loewnerRatio (a := powerMeanMap s w Av t X)
    (b := powerMeanMap s w Av t Y) hα hβ hFX.nonneg hFY.nonneg hFXβ hFYα hFYβ hFXα
    hρ1 h1 h2
  refine hfin.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **Existence of the Lim–Pálfia power mean.** -/
theorem exists_powerMean [Nontrivial A] {t α β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    ∃ X : A, IsStrictlyPositive X ∧ α • (1 : A) ≤ X ∧ X ≤ β • (1 : A)
      ∧ powerMeanMap s w Av t X = X := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨X, hX0, hXsucc⟩ : ∃ f : ℕ → A, f 0 = α • (1 : A)
      ∧ ∀ n, f (n + 1) = powerMeanMap s w Av t (f n) :=
    ⟨fun n => (powerMeanMap s w Av t)^[n] (α • (1 : A)), rfl, fun n => by
      show (powerMeanMap s w Av t)^[n + 1] (α • (1 : A))
        = powerMeanMap s w Av t ((powerMeanMap s w Av t)^[n] (α • (1 : A)))
      rw [Function.iterate_succ_apply']⟩
  -- the iterates stay in the interval
  have hXmem : ∀ n, IsStrictlyPositive (X n) ∧ α • (1 : A) ≤ X n ∧ X n ≤ β • (1 : A) := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · rw [hX0]; exact IsStrictlyPositive.smul hα isStrictlyPositive_one
        · rw [hX0]
        · rw [hX0, ← sub_nonneg, ← sub_smul]
          exact smul_nonneg (by linarith) zero_le_one
    | succ n ih =>
        obtain ⟨hp, hlo, hhi⟩ := ih
        obtain ⟨h1, h2⟩ := powerMeanMap_mem_Icc (s := s) (w := w) (Av := Av)
          ⟨le_of_lt ht, ht1⟩ hα hβ hw hwsum hA hAα hAβ hp hlo hhi
        rw [hXsucc n]
        exact ⟨isStrictlyPositive_of_smul_one_le hα h1, h1, h2⟩
  -- the Loewner ratio of consecutive iterates
  obtain ⟨R, hRdef⟩ : ∃ f : ℕ → ℝ, f = fun n =>
      max (loewnerRatio (X n) (X (n + 1))) (loewnerRatio (X (n + 1)) (X n)) := ⟨_, rfl⟩
  have hRpos : ∀ n, 0 < loewnerRatio (X n) (X (n + 1)) := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hXmem n
    obtain ⟨hp', hlo', hhi'⟩ := hXmem (n + 1)
    exact loewnerRatio_pos hα hβ hp'.nonneg hhi hlo' hlo hhi'
  have hRpos' : ∀ n, 0 < loewnerRatio (X (n + 1)) (X n) := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hXmem n
    obtain ⟨hp', hlo', hhi'⟩ := hXmem (n + 1)
    exact loewnerRatio_pos hα hβ hp.nonneg hhi' hlo hlo' hhi
  have hR1 : ∀ n, 1 ≤ R n := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hXmem n
    obtain ⟨hp', hlo', hhi'⟩ := hXmem (n + 1)
    have hmul := one_le_loewnerRatio_mul hα hβ hp.nonneg hp'.nonneg hlo hhi hlo' hhi'
    rw [hRdef]
    by_contra hlt
    have hlt' : max (loewnerRatio (X n) (X (n + 1))) (loewnerRatio (X (n + 1)) (X n)) < 1 :=
      not_le.mp hlt
    have h1 : loewnerRatio (X n) (X (n + 1)) < 1 := lt_of_le_of_lt (le_max_left _ _) hlt'
    have h2 : loewnerRatio (X (n + 1)) (X n) < 1 := lt_of_le_of_lt (le_max_right _ _) hlt'
    nlinarith [hmul, h1, h2, hRpos n, hRpos' n]
  have hRdec : ∀ n, R (n + 1) - 1 ≤ (1 - t) * (R n - 1) := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hXmem n
    obtain ⟨hp', hlo', hhi'⟩ := hXmem (n + 1)
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
    have e1 : loewnerRatio (X (n + 1)) (X (n + 1 + 1)) ≤ 1 + (1 - t) * (R n - 1) := by
      have h := hstep (X n) (X (n + 1)) hp hp' hlo hhi hlo' hhi'
        (by rw [hRdef]; exact le_max_left _ _)
      rwa [← hXsucc n, ← hXsucc (n + 1)] at h
    have e2 : loewnerRatio (X (n + 1 + 1)) (X (n + 1)) ≤ 1 + (1 - t) * (R n - 1) := by
      have h := hstep (X (n + 1)) (X n) hp' hp hlo' hhi' hlo hhi
        (by rw [hRdef]; exact le_max_right _ _)
      rwa [← hXsucc n, ← hXsucc (n + 1)] at h
    have hRn1 : R (n + 1)
        = max (loewnerRatio (X (n + 1)) (X (n + 1 + 1)))
          (loewnerRatio (X (n + 1 + 1)) (X (n + 1))) := by rw [hRdef]
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
  -- the increments are summable
  have hnorm : ∀ n, ‖X n - X (n + 1)‖ ≤ (3 * β * (R 0 - 1)) * (1 - t) ^ n := by
    intro n
    obtain ⟨hp, hlo, hhi⟩ := hXmem n
    obtain ⟨hp', hlo', hhi'⟩ := hXmem (n + 1)
    have hb := norm_sub_le_of_loewnerRatio (a := X n) (b := X (n + 1)) hα hβ hp.nonneg hp'.nonneg
      hhi hlo' hhi' hlo (hR1 n) (by rw [hRdef]; exact le_max_left _ _)
      (by rw [hRdef]; exact le_max_right _ _)
    refine hb.trans ?_
    have hg := hRgeom n
    have h3 := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 3 * β)
    have h4 : 3 * β * ((1 - t) ^ n * (R 0 - 1)) = 3 * β * (R 0 - 1) * (1 - t) ^ n := by ring
    linarith [h3, h4]
  have hsummable : Summable (fun n => dist (X n) (X n.succ)) := by
    refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_)
      (((summable_geometric_of_lt_one (r := 1 - t) (by linarith) (by linarith)).mul_left
        (3 * β * (R 0 - 1))))
    rw [dist_eq_norm]
    exact hnorm n
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsummable)
  -- the limit lies in the interval and is a fixed point
  have hLmem : α • (1 : A) ≤ L ∧ L ≤ β • (1 : A) := by
    constructor
    · have hcl : IsClosed {x : A | α • (1 : A) ≤ x} := by
        have hset : {x : A | α • (1 : A) ≤ x} = (fun x : A => x - α • (1 : A)) ⁻¹' {y : A | 0 ≤ y} := by
          ext x; simp [sub_nonneg]
        rw [hset]
        exact IsClosed.preimage (by fun_prop) CStarAlgebra.isClosed_nonneg
      exact hcl.mem_of_tendsto hL (Eventually.of_forall fun n => (hXmem n).2.1)
    · have hcl : IsClosed {x : A | x ≤ β • (1 : A)} := by
        have hset : {x : A | x ≤ β • (1 : A)}
            = (fun x : A => β • (1 : A) - x) ⁻¹' {y : A | 0 ≤ y} := by
          ext x; simp [sub_nonneg]
        rw [hset]
        exact IsClosed.preimage (by fun_prop) CStarAlgebra.isClosed_nonneg
      exact hcl.mem_of_tendsto hL (Eventually.of_forall fun n => (hXmem n).2.2)
  have hLpos : IsStrictlyPositive L := isStrictlyPositive_of_smul_one_le hα hLmem.1
  refine ⟨L, hLpos, hLmem.1, hLmem.2, ?_⟩
  have hFcont : Tendsto (fun n => powerMeanMap s w Av t (X n)) atTop
      (nhds (powerMeanMap s w Av t L)) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (?_ : Tendsto (fun n => (3 * β * ((1 - t) / α)) * dist (X n) L) atTop (nhds 0))
    · rw [dist_eq_norm, dist_eq_norm]
      obtain ⟨hp, hlo, hhi⟩ := hXmem n
      exact norm_powerMeanMap_sub_le (s := s) (w := w) (Av := Av) ht ht1 hα hβ hw hwsum hA
        hAα hAβ hp hLpos hlo hhi hLmem.1 hLmem.2
    · have hd : Tendsto (fun n => dist (X n) L) atTop (nhds 0) :=
        tendsto_iff_dist_tendsto_zero.mp hL
      simpa using hd.const_mul (3 * β * ((1 - t) / α))
  have hshift : Tendsto (fun n => X (n + 1)) atTop (nhds L) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hL
  have heq : Tendsto (fun n => powerMeanMap s w Av t (X n)) atTop (nhds L) := by
    exact hshift.congr fun n => hXsucc n
  exact tendsto_nhds_unique hFcont heq

/-- **The Lim–Pálfia power mean `P_t(ω; 𝔸)`.**  For `0 < t ≤ 1` the equation
`X = ∑ᵢ wᵢ (X #_t Aᵢ)` has exactly one solution in the Loewner interval spanned by the data. -/
theorem existsUnique_powerMean [Nontrivial A] {t α β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    ∃! X : A, (α • (1 : A) ≤ X ∧ X ≤ β • (1 : A)) ∧ powerMeanMap s w Av t X = X := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨X, hXpos, hXα, hXβ, hXfix⟩ :=
    exists_powerMean (s := s) (w := w) (Av := Av) ht ht1 hα hαβ hw hwsum hA hAα hAβ
  refine ⟨X, ⟨⟨hXα, hXβ⟩, hXfix⟩, ?_⟩
  rintro Y ⟨⟨hYα, hYβ⟩, hYfix⟩
  exact powerMeanMap_fixedPoint_unique ht ht1 hα hβ hw hwsum hA hAα hAβ
    (isStrictlyPositive_of_smul_one_le hα hYα) hXpos hYα hYβ hXα hXβ hYfix hXfix

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
