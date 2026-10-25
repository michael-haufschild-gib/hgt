import GaloisForLFunctions.RHTower.Zeta23SimpleOrCriticalCensus

/-!
# Simple or critical zeros: the optimal rank–trace level `c = 2 + √2`

The multiplicity-aware rank–trace inequality of Alpöge–Furman at level `c`,
`2c tr Â − ‖Â‖_F² ≤ Σ_{on-line} k_c(m) + c²·p`, charges a point on the line of multiplicity `m` at
most `(2c − 1)m` and an off-line pair of multiplicity `m` exactly `c²`.  At `c = 2 + √2` a simple
off-line pair costs exactly `(2c − 1)` per zero copy, `c² = 2(2c − 1)`, while an off-line pair of
multiplicity `m ≥ 2` leaves `(2c − 1)·2m − c² ≥ (3/2 + √2)·2m` unused.  Hence

`2c tr Â − ‖Â‖_F² ≤ (2c − 1)·N − (3/2 + √2)·M_off`               (`sqrtTwo_budget_le`),

and through the Montgomery–Taylor window (`‖Ĝ‖² ≤ (2 − HD(1) + o(1))N`, `tr Ĝ = (1 + o(1))N`)

`(3/2 + √2)·M_off(T,2T) ≤ (1 − HD(1) + ε)·N(T,2T)`             (`sqrtTwo_offLineMultipleMass_le`).

So at least `1 − (1 − HD(1))/(3/2 + √2) − ε = 0.8876…` of the zero copies of `ζ` in `(T, 2T]` are
simple or lie on the critical line (`simple_or_critical_optimal`).  Among the levels `c`, the bound
`(1 − HD(1))/(2c − 1 − c²/4)` with `c² ≤ 2(2c − 1)` is minimised at `c = 2 + √2`.  Unconditional.
-/

open Filter Asymptotics Topology Real RHLinalg Finset
open scoped BigOperators ComplexOrder

noncomputable section

namespace RHTower

open Zeta23 Zeta23.Assembly

/-- The rank–trace level `2 + √2`. -/
def sqrtTwoLevel : ℝ := 2 + Real.sqrt 2

lemma sqrtTwoLevel_pos : 0 < sqrtTwoLevel := by unfold sqrtTwoLevel; positivity

lemma sqrtTwoLevel_sq : sqrtTwoLevel ^ 2 = 2 * (2 * sqrtTwoLevel - 1) := by
  unfold sqrtTwoLevel
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [h]

/-- `2c − 1 − c²/4 = 3/2 + √2` at `c = 2 + √2`. -/
lemma sqrtTwoLevel_gap : 2 * sqrtTwoLevel - 1 - sqrtTwoLevel ^ 2 / 4 = 3 / 2 + Real.sqrt 2 := by
  rw [sqrtTwoLevel_sq]; unfold sqrtTwoLevel; ring

/-! ## Optimality of the level `2 + √2`

Two elementary facts show that no level of the rank–trace certificate beats `3/2 + √2`.  At a level
`c` where a simple off-line pair is not charged more than two simple critical zeros
(`c² ≤ 2(2c − 1)`), the unused budget per copy of a doubled pair is `2c − 1 − c²/4 ≤ 3/2 + √2`
(`levelGap_le`).  With the trace-aware bound `bφ_c(T/b)`, the worst mixture of simple and doubled
pairs (simple fraction `α ∈ [0, 1]`) bounds `M_off/(1 − HD)` by `(1 − α²)/(3 − α) ≤ 6 − 4√2 = (3/2 + √2)⁻¹`
(`mixture_le`, `six_sub_four_sqrt_two_eq`). -/

/-- `(3/2 + √2)⁻¹ = 6 − 4√2`. -/
lemma six_sub_four_sqrt_two_eq : (3 / 2 + Real.sqrt 2)⁻¹ = 6 - 4 * Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  exact inv_eq_of_mul_eq_one_right (by nlinarith [h])

/-- On the admissible levels `c² ≤ 2(2c − 1)`, the gap `2c − 1 − c²/4` is at most `3/2 + √2`. -/
lemma levelGap_le {c : ℝ} (hc : c ^ 2 ≤ 2 * (2 * c - 1)) :
    2 * c - 1 - c ^ 2 / 4 ≤ 3 / 2 + Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- admissible levels satisfy `c ≤ 2 + √2`, and the gap increases up to `c = 4`
  have hcle : c ≤ 2 + Real.sqrt 2 := by nlinarith [sq_nonneg (c - 2 - Real.sqrt 2)]
  nlinarith [sq_nonneg (c - 2 - Real.sqrt 2)]

/-- The worst mixture: `(1 − α²)/(3 − α) ≤ 6 − 4√2` for `α ≤ 1`, with equality at `α = 3 − 2√2`. -/
lemma mixture_le {α : ℝ} (h1 : α ≤ 1) :
    (1 - α ^ 2) / (3 - α) ≤ 6 - 4 * Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [div_le_iff₀ (by linarith)]
  -- `(6 − 4√2)(3 − α) − (1 − α²) = (α − (3 − 2√2))²`
  nlinarith [sq_nonneg (α - (3 - 2 * Real.sqrt 2))]

/-! ## Block level -/

section Block

open Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- `k_c(m) ≤ (2c − 1)m` for `c ≥ 1`, `m ≥ 1`: a point on the line costs at most `2c − 1` per copy. -/
lemma kc_le_two_mul_sub_one_mul {c m : ℝ} (hc : 1 ≤ c) (hm : 1 ≤ m) :
    kc c m ≤ (2 * c - 1) * m := by
  rcases le_total m c with h | h
  · rw [kc_of_le h]; nlinarith
  · rw [kc_of_ge h]; nlinarith

/-- **Cost table, doubles against pairs**: for `c ≥ 2` a critical double costs `k_c(2)/2 = 2c − 2`
per copy and an off-line pair `c²/2`, with `c²/2 − k_c(2)/2 = (c − 2)²/2 ≥ 0`.  No level charges a
near pair less than a double: the certificate form of the continuity barrier. -/
lemma kc_two_div_two_add_sq {c : ℝ} (hc : 2 ≤ c) : kc c 2 / 2 + (c - 2) ^ 2 / 2 = c ^ 2 / 2 := by
  rw [kc_of_le hc]; ring

/-- **Cost table, simple zeros against pairs**: for `c ≥ 1` an off-line pair costs more per copy
than a simple critical zero (`k_c(1) = 2c − 1`) exactly when `c > 2 + √2`. -/
lemma kc_one_lt_sq_div_two_iff {c : ℝ} (hc : 1 ≤ c) :
    kc c 1 < c ^ 2 / 2 ↔ 2 + Real.sqrt 2 < c := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [kc_of_le hc]
  constructor
  · intro hlt
    -- `c² − 4c + 2 > 0` with `c ≥ 1` forces `c > 2 + √2`
    by_contra hle
    rw [not_lt] at hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show (0 : ℝ) ≤ c - (2 - Real.sqrt 2) by linarith)]
  · intro hlt
    nlinarith [mul_pos (sub_pos.mpr hlt) (show (0 : ℝ) < c - (2 - Real.sqrt 2) by linarith)]

/-- The simple off-line coefficient `2c − 1 − c²/2` of the level-`c` certificate is at most `1`, with
equality at `c = 2`: no level improves `S_off + M_off ≤ 1 − HD(1)`. -/
lemma simpleLevelGap_le (c : ℝ) : 2 * c - 1 - c ^ 2 / 2 ≤ 1 := by
  nlinarith [sq_nonneg (c - 2)]

/-- The off-line multiple mass of a block, through its pair representatives. -/
lemma blockOffLineMultipleMass_eq_sum_pairReps (D : ZeroBlockData ι d) (Pr : D.PairReps) :
    blockOffLineMultipleMass D = ∑ z ∈ Pr.R, 2 * (if 2 ≤ D.m z then D.m z else 0) := by
  classical
  set g : ι → ℕ := fun z => if ¬ D.σ z = z ∧ 2 ≤ D.m z then D.m z else 0 with hg
  have h1 : blockOffLineMultipleMass D = ∑ z, g z := by
    unfold blockOffLineMultipleMass
    rw [Finset.sum_filter]
  rw [h1, D.sum_split Pr g]
  have hon : ∑ z ∈ D.onLine, g z = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have : D.σ z = z := (D.mem_onLine).mp hz
    simp [hg, this]
  rw [hon, zero_add]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hoff : ¬ D.σ z = z := Pr.off z hz
  have hoff' : ¬ D.σ (D.σ z) = D.σ z := by
    rw [D.σ_invol z]; exact fun h => hoff h.symm
  simp only [hg, hoff, hoff', not_false_eq_true, true_and, D.m_σ z]
  ring

/-- **The `2 + √2` budget**: `2c tr Â − ‖Â‖_F² ≤ (2c − 1)N − (3/2 + √2)M_off` at `c = 2 + √2`. -/
theorem sqrtTwo_budget_le (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    2 * sqrtTwoLevel * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) ≤
      (2 * sqrtTwoLevel - 1) * (D.Ncount : ℝ)
        - (3 / 2 + Real.sqrt 2) * (blockOffLineMultipleMass D : ℝ) := by
  classical
  set κ := sqrtTwoLevel with hκ
  have hκ1 : 1 ≤ κ := by
    rw [hκ]; unfold sqrtTwoLevel; linarith [Real.sqrt_nonneg 2]
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c)
    (D.xsq_vhat_le hc hPois) (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc)
    (c := κ) (by linarith)
  rw [← D.blockP_eq_Pmat hc] at hR
  -- points on the line
  have hon : ∑ z : D.onLine, kc κ (D.mhat z) ≤ (2 * κ - 1) * (D.Non : ℝ) := by
    have h1 : ∑ z : D.onLine, kc κ (D.mhat z) ≤ ∑ z : D.onLine, (2 * κ - 1) * D.mhat z :=
      Finset.sum_le_sum fun z _ => kc_le_two_mul_sub_one_mul hκ1
        (by simp only [ZeroBlockData.mhat]; exact_mod_cast D.one_le_m z)
    refine h1.trans (le_of_eq ?_)
    rw [← Finset.mul_sum]
    congr 1
    unfold ZeroBlockData.Non ZeroBlockData.mhat
    push_cast
    exact Finset.sum_coe_sort D.onLine (fun z => (D.m z : ℝ))
  -- off-line pairs
  have hN : (D.Ncount : ℝ) = (D.Non : ℝ) + ∑ z ∈ Pr.R, 2 * (D.m z : ℝ) := by
    have h : D.Ncount = D.Non + ∑ z ∈ Pr.R, 2 * D.m z := by
      unfold ZeroBlockData.Ncount ZeroBlockData.Non
      rw [D.sum_split Pr (fun z => D.m z)]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [D.m_σ z]; ring
    rw [h]; push_cast; rfl
  have hM : (blockOffLineMultipleMass D : ℝ) =
      ∑ z ∈ Pr.R, 2 * ((if 2 ≤ D.m z then D.m z else 0 : ℕ) : ℝ) := by
    rw [blockOffLineMultipleMass_eq_sum_pairReps D Pr]; push_cast; rfl
  have hsq := sqrtTwoLevel_sq
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpair : ∀ z ∈ Pr.R, κ ^ 2 + (3 / 2 + Real.sqrt 2) * (2 * ((if 2 ≤ D.m z then D.m z else 0 : ℕ) : ℝ))
      ≤ (2 * κ - 1) * (2 * (D.m z : ℝ)) := by
    intro z _
    have hm := D.one_le_m z
    have hκe : 2 * κ - 1 = 3 + 2 * Real.sqrt 2 := by rw [hκ]; unfold sqrtTwoLevel; ring
    split_ifs with h2
    · have h2' : (2 : ℝ) ≤ D.m z := by exact_mod_cast h2
      rw [hsq, hκe]; nlinarith
    · have h1 : D.m z = 1 := by omega
      rw [h1, hsq]; push_cast; nlinarith
  have hsum := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum
  have hp : (Pr.R.card : ℝ) = (Pr.p : ℝ) := rfl
  rw [hp] at hsum
  have e1 : ∑ i ∈ Pr.R, (2 * κ - 1) * (2 * (D.m i : ℝ)) =
      (2 * κ - 1) * ∑ z ∈ Pr.R, 2 * (D.m z : ℝ) := by rw [Finset.mul_sum]
  have e2 : ∑ z ∈ Pr.R, 2 * ((if 2 ≤ D.m z then D.m z else 0 : ℕ) : ℝ) =
      2 * ∑ z ∈ Pr.R, ((if 2 ≤ D.m z then D.m z else 0 : ℕ) : ℝ) := by rw [Finset.mul_sum]
  rw [e1] at hsum
  rw [hN, hM, e2]
  have : κ ^ 2 * (Pr.p : ℝ) = (Pr.p : ℝ) * κ ^ 2 := by ring
  linarith

end Block

/-! ## The concrete Gram: seam at level `2 + √2` -/

section Seam

open Zeta23.ZeroSide

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- **The `2 + √2` certificate with the off-line multiple mass**:
`2c tr Â − ‖Â‖_F² − (2c − 1)N(I′) + (3/2 + √2)M_off(I′) ≤ 0`. -/
theorem hatAz_sqrtTwo_offLineMultiple (Z : ZeroConfig) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P) (hc : 0 < P.a T * P.L T ^ 2) :
    2 * sqrtTwoLevel * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
      - (2 * sqrtTwoLevel - 1) * (Z.NIprime T : ℝ)
      + (3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) : ℝ) ≤ 0 := by
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj),
    ← blockOffLineMultipleMass_mkData Z hconj]
  unfold hatP hatQ blockData
  have h := sqrtTwo_budget_le _ (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj hreal hPois)
  linarith

/-- **Seam A at level `2 + √2`**: on the dyadic window,
`2c tr Ĝ − ‖Ĝ‖² − (2c − 1)(N + N_II) − B(2c + 2√‖Ĝ‖² + B) ≤ −(3/2 + √2)M_off`. -/
theorem seamA_sqrtTwo_offLineMultiple (hT : 0 ≤ T) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    2 * sqrtTwoLevel * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - (2 * sqrtTwoLevel - 1) * ((Z.N T (2 * T) : ℝ) + (NII Z T : ℝ))
      - θ₀ / (P.a T * P.L T)
          * (2 * sqrtTwoLevel + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ -((3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z T (2 * T) : ℝ)) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_sqrtTwo_offLineMultiple Z hconj hreal hPois (mul_pos ha (pow_pos hL 2))
  have hpert := ctr_sub_frobSq_perturb (2 * sqrtTwoLevel) (by linarith [sqrtTwoLevel_pos]) hGAE
    hB₀ (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  have hmono : (offLineMultipleMass Z T (2 * T) : ℝ) ≤
      (offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) : ℝ) := by
    exact_mod_cast offLineMultipleMass_mono Z (by linarith [D0_nonneg T])
      (by linarith [D0_nonneg T])
  have hK : (0 : ℝ) ≤ 3 / 2 + Real.sqrt 2 := by positivity
  rw [hNI] at hcore
  nlinarith [hcore, hpert, mul_le_mul_of_nonneg_left hmono hK]

end Seam

/-! ## The Theorem-D endgame at level `2 + √2` -/

section TheoremD

open Zeta23.ThmD

/-- The seam, the trace asymptotics and the Frobenius ceiling give
`(3/2 + √2)M_off ≤ (c⁻¹ − 1)N + err`. -/
lemma sqrtTwo_lower {M N NII trGh frGh B cinv R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 2 * sqrtTwoLevel * trGh - frGh - (2 * sqrtTwoLevel - 1) * (N + NII)
      - B * (2 * sqrtTwoLevel + 2 * Real.sqrt frGh + B) ≤ -((3 / 2 + Real.sqrt 2) * M))
    (htr : |trGh - N| ≤ R₁) (hfr : frGh ≤ cinv * N + R₂) :
    (3 / 2 + Real.sqrt 2) * M ≤ (cinv - 1) * N + (2 * sqrtTwoLevel * R₁ + R₂
      + (2 * sqrtTwoLevel - 1) * NII
      + B * (2 * sqrtTwoLevel + 2 * Real.sqrt (cinv * N + R₂) + B)) := by
  have h1 : N - R₁ ≤ trGh := by
    have := (abs_le.mp htr).1
    linarith
  have h2 : Real.sqrt frGh ≤ Real.sqrt (cinv * N + R₂) := Real.sqrt_le_sqrt hfr
  have hκ := sqrtTwoLevel_pos
  nlinarith [h0, h1, h2, hB, mul_le_mul_of_nonneg_left h2 hB, mul_le_mul_of_nonneg_left h1
    (by linarith : (0 : ℝ) ≤ 2 * sqrtTwoLevel)]

/-- **Off-line multiple mass at level `2 + √2`, Theorem-D window, abstract**:
`(3/2 + √2)M_off ≤ (c⁻¹ − 1 + ε)N`. -/
theorem thmD_sqrtTwo_offLineMultiple_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z T (2 * T) : ℝ)
        ≤ (c⁻¹ - 1 + ε) * (Z.N T (2 * T) : ℝ) := by
  intro ε hε
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set κ := sqrtTwoLevel with hκdef
  have hκ0 : 0 < κ := sqrtTwoLevel_pos
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (2 * κ * R₁ T + R₂ T + (2 * κ - 1) * (NII Z T : ℝ)
      + B T * (2 * κ + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T
    with herr
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  -- (1) the seam with the off-line multiple mass, eventually in `T`
  have hmain : ∀ᶠ T in atTop,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z T (2 * T) : ℝ) ≤ (c⁻¹ - 1) * N T + err T := by
    filter_upwards [hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hA := seamA_sqrtTwo_offLineMultiple hT0 (fun z => GzGp.phiHat_conj _ T z)
      (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD hLpos
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := sqrtTwo_lower hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (cinv T - 1) * N T ≤ (c⁻¹ - 1) * N T + |cinv T - c⁻¹| * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  -- (2) `err = o(N)`, exactly as in the Theorem-D endgame
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have oB : B =o[atTop] N := by
    refine ((isLittleO_one_iff ℝ).2 o4).trans_isBigO (IsBigO.of_bound 1 ?_)
    filter_upwards [hNtop.eventually_ge_atTop 1] with T h1
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by linarith), one_mul]; exact h1
  -- the level `2κ` exceeds Zeta23's `4` by `2κ − 4`
  have o5' : (fun T => 2 * κ * R₁ T + R₂ T + (2 * κ - 1) * (NII Z T : ℝ)
      + B T * (2 * κ + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) =o[atTop] N := by
    have := o5.add ((((o1.const_mul_left (2 * κ - 4)).add (o3.const_mul_left (2 * κ - 4))).add
      (oB.const_mul_left (2 * κ - 4))))
    exact this.congr_left fun T => by ring
  have herr_o : err =o[atTop] N := o5'.add o6
  -- (3) conclude
  have hfin : ∀ᶠ T in atTop, err T ≤ ε * N T := (herr_o.def hε).mono fun T h => by
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at h
    exact (le_abs_self _).trans h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hmain.and hfin)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hT₀ T hT
  simp only [hNdef] at h1 h2
  nlinarith [h1, h2]

/-- Level `2 + √2` at fixed `λ ∈ (0,1)`, abstract zero configuration:
`(3/2 + √2)M_off ≤ (1 − HD(λ) + ε)N`. -/
theorem thmD_sqrtTwo_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z T (2 * T) : ℝ)
        ≤ (1 - HD P.lam + ε) * (Z.N T (2 * T) : ℝ) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_sqrtTwo_offLineMultiple_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail
    hθ₀ hNII hGzGp hId hcalE
  have hHD : 1 - HD P.lam = (cStar P.lam)⁻¹ - 1 := by simp only [HD, one_div]; ring
  simpa only [hHD] using h

/-- Level `2 + √2` for `ζ` at fixed `λ ∈ (0,1)`, unconditional. -/
theorem thmD_sqrtTwo_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)
        ≤ (1 - HD lam + ε) * (Ncount T (2 * T) : ℝ) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmD_sqrtTwo_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1

/-- **`(3/2 + √2)·M_off ≤ (1 − HD(1) + ε)·N`** for `ζ`, unconditional. -/
theorem sqrtTwo_offLineMultipleMass_le :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)
        ≤ (1 - HD 1 + ε) * (Ncount T (2 * T) : ℝ) := by
  -- run `eps_form_HD` on `N − (3/2 + √2)M_off`
  have h := eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (Ncount T (2 * T) : ℝ)
      - (3 / 2 + Real.sqrt 2) * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun lam hl1 hl2 ε hε => by
      obtain ⟨T₀, hT₀⟩ := thmD_sqrtTwo_lam (by linarith) hl2 ε hε
      exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩)
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

/-- **At least `1 − (1 − HD(1))/(3/2 + √2) − ε = 0.8876…` of the zero copies of `ζ` in `(T, 2T]`
are simple or lie on the critical line**, unconditional. -/
theorem simple_or_critical_optimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (1 - HD 1) / (3 / 2 + Real.sqrt 2) - ε) * (Ncount T (2 * T) : ℝ)
        ≤ (Ncount T (2 * T) : ℝ) - (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
  intro ε hε
  have hK : (1 : ℝ) ≤ 3 / 2 + Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  obtain ⟨T₀, hT₀⟩ := sqrtTwo_offLineMultipleMass_le ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN : (0 : ℝ) ≤ Ncount T (2 * T) := Nat.cast_nonneg _
  have hKpos : (0 : ℝ) < 3 / 2 + Real.sqrt 2 := by linarith
  set K := 3 / 2 + Real.sqrt 2
  set M : ℝ := (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)
  set N : ℝ := (Ncount T (2 * T) : ℝ)
  have h1 : M ≤ (1 - HD 1 + ε) * N / K := by rw [le_div_iff₀ hKpos]; linarith
  have h2 : (1 - HD 1 + ε) * N / K = (1 - HD 1) * N / K + ε * N / K := by ring
  have h3 : ε * N / K ≤ ε * N := div_le_self (mul_nonneg hε.le hN) hK
  have e : (1 - HD 1) / K * N = (1 - HD 1) * N / K := by ring
  nlinarith

/-- **Cumulative form**: at least `1 − (1 − HD(1))/(3/2 + √2) − ε` of the zero copies of `ζ` up to
height `T` are simple or lie on the critical line. -/
theorem simple_or_critical_optimal_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (1 - HD 1) / (3 / 2 + Real.sqrt 2) - ε) * (Ncount 0 T : ℝ)
        ≤ (Ncount 0 T : ℝ) - (offLineMultipleMass zetaZeroConfig 0 T : ℝ) := by
  have hNadd : ∀ a b d : ℝ, a ≤ b → b ≤ d →
      (Ncount a d : ℝ) = (Ncount a b : ℝ) + (Ncount b d : ℝ) := fun a b d hab hbd => by
    have := Zeta23.Assembly.N_add zetaZeroConfig hab hbd
    rw [zetaZeroConfig_N, zetaZeroConfig_N, zetaZeroConfig_N] at this
    exact_mod_cast this
  exact Zeta23.Assembly.dyadic
    (f := fun a b => (Ncount a b : ℝ) - (offLineMultipleMass zetaZeroConfig a b : ℝ))
    (g := fun a b => (Ncount a b : ℝ))
    (fun a b d hab hbd => by
      rw [hNadd a b d hab hbd, offLineMultipleMass_add zetaZeroConfig hab hbd]; push_cast; ring)
    hNadd
    (fun a b => by
      have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple a b
      have hS : (0 : ℝ) ≤ offLineSimpleCount zetaZeroConfig a b := Nat.cast_nonneg _
      have hN0 : (0 : ℝ) ≤ N0 a b := Nat.cast_nonneg _
      linarith)
    (fun _ _ => Nat.cast_nonneg _) (tendsto_Ncount_zero_atTop zetaSeam paperInputs_zeta.RvM)
    simple_or_critical_optimal

end TheoremD

end RHTower

end
