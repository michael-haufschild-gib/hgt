import GaloisForLFunctions.RHTower.LiRemoteQuartetGaugedCarrier
import GaloisForLFunctions.RHTower.LiRemoteQuartetLogPhaseAlignment

/-!
# Li remote-quartet transverse visibility law

This final assembly proves the card's sharp prefix-blindness and logarithmic-overhead sign-flip
statements for the literal divisor-normalized coefficient of the actual reflected-Gamma carrier
with its normalized remote-quartet gauge.  All constants are explicit.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Card equations `(25)`--`(26)`: every positive degree in a prefix of transverse size
`N a / T² → 0` has a strictly positive coefficient on the explicit gauged carrier. -/
theorem eventually_liRemoteQuartetGaugedCarrierCoefficient_pos_prefix
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} (N : ι → ℕ)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2)
    (hsub : Tendsto (fun i => (N i : ℝ) * a i / T i ^ 2) l (nhds 0)) :
    ∀ᶠ i in l, ∀ n : ℕ, 1 ≤ n → n ≤ N i →
      0 < liRemoteQuartetGaugedCarrierCoefficient alpha n (a i) (T i) := by
  have hrad := tendsto_liRemoteRadialScale hT ha
  have hprod := hsub.mul hrad
  have hTpos : ∀ᶠ i in l, 0 < T i := hT.eventually_gt_atTop 0
  have hnell : Tendsto (fun i => (N i : ℝ) *
      liRemoteRadialCoordinate (a i) (T i)) l (nhds 0) := by
    have h : Tendsto (fun i => (N i : ℝ) *
        liRemoteRadialCoordinate (a i) (T i)) l (nhds (0 * 1)) :=
      hprod.congr' (by
      filter_upwards [ha, hTpos] with i hai hTi
      have ha0 := ne_of_gt hai.1
      have hT0 := ne_of_gt hTi
      field_simp [ha0, hT0])
    simpa only [zero_mul] using h
  have hcosh : Tendsto (fun i => Real.cosh ((N i : ℝ) *
      liRemoteRadialCoordinate (a i) (T i))) l (nhds 1) := by
    have hraw := (Real.continuous_cosh.tendsto 0).comp hnell
    have hfun : Tendsto (fun i => Real.cosh ((N i : ℝ) *
        liRemoteRadialCoordinate (a i) (T i))) l (nhds (Real.cosh 0)) :=
      hraw.congr' (Filter.Eventually.of_forall fun _ => rfl)
    simpa only [Real.cosh_zero] using hfun
  have herr : Tendsto (fun i => 4 * (Real.cosh ((N i : ℝ) *
      liRemoteRadialCoordinate (a i) (T i)) - 1)) l (nhds 0) := by
    have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
    have h := (hcosh.sub hone).const_mul (4 : ℝ)
    simpa using h
  have hmargin := liReflectedGammaCarrierUniformMargin_pos halpha
  have hsmall : ∀ᶠ i in l,
      4 * (Real.cosh ((N i : ℝ) *
        liRemoteRadialCoordinate (a i) (T i)) - 1) <
        liReflectedGammaCarrierUniformMargin alpha :=
    (tendsto_order.1 herr).2 _ hmargin
  have hcoord := eventually_liRemoteCoordinates_pos hT ha
  filter_upwards [hsmall, hcoord] with i hsmalli hcoordi
  intro n hn hnN
  have hcarrier := liReflectedGammaCarrierUniformMargin_le halpha hn
  have hquartet := liRemoteQuartetProfile_lower_bound_of_nonneg hnN
    hcoordi.1.le (liRemoteAngularCoordinate (a i) (T i))
  rw [liRemoteQuartetGaugedCarrierCoefficient]
  linarith

/-- The logarithmically phase-aligned degree is eventually positive. -/
theorem eventually_liRemoteLogPhaseAlignedDegree_pos
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l, 1 ≤ liRemoteLogPhaseAlignedDegree (a i) (T i) := by
  have hratio := tendsto_liRemoteLogPhaseAlignedDegree_div_visibilityLog hT ha
  have hratioLower : ∀ᶠ i in l, (3 : ℝ) <
      (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) /
        (liRemoteVisibilityScale (a i) (T i) *
          Real.log (liRemoteVisibilityScale (a i) (T i))) :=
    (tendsto_order.1 hratio).1 3 (by norm_num)
  have hH := tendsto_liRemoteVisibilityScale_atTop hT ha
  have hHgt : ∀ᶠ i in l, 1 < liRemoteVisibilityScale (a i) (T i) :=
    hH.eventually_gt_atTop 1
  filter_upwards [hratioLower, hHgt] with i hri hHi
  have hlog : 0 < Real.log (liRemoteVisibilityScale (a i) (T i)) :=
    Real.log_pos hHi
  have hden : 0 < liRemoteVisibilityScale (a i) (T i) *
      Real.log (liRemoteVisibilityScale (a i) (T i)) := mul_pos (by linarith) hlog
  have hquot : 0 < (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) /
      (liRemoteVisibilityScale (a i) (T i) *
        Real.log (liRemoteVisibilityScale (a i) (T i))) := lt_trans (by norm_num) hri
  have hnreal : 0 < (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) := by
    rcases div_pos_iff.mp hquot with hgood | hbad
    · exact hgood.1
    · exact False.elim ((not_lt_of_ge hden.le) hbad.2)
  exact_mod_cast hnreal

/-- Card equation `(35)` with an explicit constant: the reflected-Gamma carrier coefficient at
the logarithmically aligned degree is eventually at most `60 H log H`. -/
theorem eventually_liReflectedGammaCarrierCoefficient_logPhaseAligned_le
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l,
      liReflectedGammaCarrierCoefficient alpha
          (liRemoteLogPhaseAlignedDegree (a i) (T i)) ≤
        60 * (liRemoteVisibilityScale (a i) (T i) *
          Real.log (liRemoteVisibilityScale (a i) (T i))) := by
  have hratio := tendsto_liRemoteLogPhaseAlignedDegree_div_visibilityLog hT ha
  have hratioUpper : ∀ᶠ i in l,
      (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) /
          (liRemoteVisibilityScale (a i) (T i) *
            Real.log (liRemoteVisibilityScale (a i) (T i))) < 5 :=
    (tendsto_order.1 hratio).2 5 (by norm_num)
  have hpos := eventually_liRemoteLogPhaseAlignedDegree_pos hT ha
  have hH := tendsto_liRemoteVisibilityScale_atTop hT ha
  have hHgt : ∀ᶠ i in l, 1 < liRemoteVisibilityScale (a i) (T i) :=
    hH.eventually_gt_atTop 1
  filter_upwards [hratioUpper, hpos, hHgt] with i hri hni hHi
  have hlog : 0 < Real.log (liRemoteVisibilityScale (a i) (T i)) :=
    Real.log_pos hHi
  have hden : 0 < liRemoteVisibilityScale (a i) (T i) *
      Real.log (liRemoteVisibilityScale (a i) (T i)) := mul_pos (by linarith) hlog
  have hnUpper : (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) <
      5 * (liRemoteVisibilityScale (a i) (T i) *
        Real.log (liRemoteVisibilityScale (a i) (T i))) :=
    (div_lt_iff₀ hden).mp hri
  have hcarrier := liReflectedGammaCarrierCoefficient_upper halpha hni
  linarith

/-- Card equation `(36)`: the explicit logarithmically phase-aligned coefficient of the actual
gauged carrier is eventually strictly negative. -/
theorem eventually_liRemoteLogPhaseAlignedGaugedCarrierCoefficient_neg
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l,
      liRemoteQuartetGaugedCarrierCoefficient alpha
          (liRemoteLogPhaseAlignedDegree (a i) (T i)) (a i) (T i) < 0 := by
  have hnormalized := tendsto_liRemoteLogPhaseAlignedQuartetProfile_normalized hT ha
  have hprofileRatio : ∀ᶠ i in l, (1 / 2 : ℝ) <
      liRemoteQuartetProfile (liRemoteLogPhaseAlignedDegree (a i) (T i))
          (liRemoteRadialCoordinate (a i) (T i))
          (liRemoteAngularCoordinate (a i) (T i)) /
        (-2 * liRemoteVisibilityScale (a i) (T i) ^ 4) :=
    (tendsto_order.1 hnormalized).1 (1 / 2) (by norm_num)
  have hcarrier :=
    eventually_liReflectedGammaCarrierCoefficient_logPhaseAligned_le halpha hT ha
  have hH := tendsto_liRemoteVisibilityScale_atTop hT ha
  have hHgt : ∀ᶠ i in l, 8 < liRemoteVisibilityScale (a i) (T i) :=
    hH.eventually_gt_atTop 8
  filter_upwards [hprofileRatio, hcarrier, hHgt] with i hqi hci hHi
  let H := liRemoteVisibilityScale (a i) (T i)
  have hHpos : 0 < H := by dsimp [H]; linarith
  have hH4pos : 0 < H ^ 4 := pow_pos hHpos _
  have hdenneg : -2 * H ^ 4 < 0 := by nlinarith
  have hquartet :
      liRemoteQuartetProfile (liRemoteLogPhaseAlignedDegree (a i) (T i))
          (liRemoteRadialCoordinate (a i) (T i))
          (liRemoteAngularCoordinate (a i) (T i)) < -H ^ 4 := by
    have hm := (lt_div_iff_of_neg hdenneg).mp hqi
    dsimp [H] at hm ⊢
    nlinarith
  have hlog : Real.log H ≤ H := Real.log_le_self hHpos.le
  have hcarrierLt :
      liReflectedGammaCarrierCoefficient alpha
          (liRemoteLogPhaseAlignedDegree (a i) (T i)) < H ^ 4 := by
    dsimp [H] at hci ⊢
    have hpoly : 60 * H ^ 2 < H ^ 4 := by
      have hsq : 60 < H ^ 2 := by nlinarith [sq_nonneg H]
      have hm := mul_lt_mul_of_pos_right hsq (sq_pos_of_pos hHpos)
      nlinarith
    calc
      liReflectedGammaCarrierCoefficient alpha
          (liRemoteLogPhaseAlignedDegree (a i) (T i))
          ≤ 60 * (H * Real.log H) := by simpa [H] using hci
      _ ≤ 60 * H ^ 2 := by nlinarith
      _ < H ^ 4 := hpoly
  rw [liRemoteQuartetGaugedCarrierCoefficient]
  linarith

/-- Algebraic approximation `T² / a` to the inverse radial visibility scale. -/
def liRemoteAlgebraicVisibilityScale (a T : ℝ) : ℝ := T ^ 2 / a

theorem tendsto_liRemoteAlgebraicVisibilityScale_atTop
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteAlgebraicVisibilityScale (a i) (T i)) l atTop := by
  refine tendsto_atTop_mono' l ?_ hT
  filter_upwards [ha, hT.eventually_gt_atTop 1] with i hai hTi
  unfold liRemoteAlgebraicVisibilityScale
  rw [le_div_iff₀ hai.1]
  nlinarith

/-- Equation `(6)` in ratio form: `H / (T²/a) → 1`. -/
theorem tendsto_liRemoteVisibilityScale_div_algebraic
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteVisibilityScale (a i) (T i) /
      liRemoteAlgebraicVisibilityScale (a i) (T i)) l (nhds 1) := by
  have hrad := tendsto_liRemoteRadialScale hT ha
  have hinv := hrad.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hcoord := eventually_liRemoteCoordinates_pos hT ha
  have hTpos : ∀ᶠ i in l, 0 < T i := hT.eventually_gt_atTop 0
  have h : Tendsto (fun i => liRemoteVisibilityScale (a i) (T i) /
      liRemoteAlgebraicVisibilityScale (a i) (T i)) l (nhds (1 : ℝ)⁻¹) :=
    hinv.congr' (by
      filter_upwards [ha, hcoord, hTpos] with i hai hci hTi
      unfold liRemoteVisibilityScale liRemoteAlgebraicVisibilityScale
      field_simp [ne_of_gt hai.1, ne_of_gt hci.1, ne_of_gt hTi])
  simpa using h

/-- Card equation `(37)` with an explicit universal constant: the selected negative degree is
eventually below `20 (T²/a) log(T²/a)`. -/
theorem eventually_liRemoteLogPhaseAlignedDegree_lt_algebraicLog
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l,
      (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) <
        20 * (liRemoteAlgebraicVisibilityScale (a i) (T i) *
          Real.log (liRemoteAlgebraicVisibilityScale (a i) (T i))) := by
  have hnratio := tendsto_liRemoteLogPhaseAlignedDegree_div_visibilityLog hT ha
  have hnupper : ∀ᶠ i in l,
      (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) /
          (liRemoteVisibilityScale (a i) (T i) *
            Real.log (liRemoteVisibilityScale (a i) (T i))) < 5 :=
    (tendsto_order.1 hnratio).2 5 (by norm_num)
  have hHSratio := tendsto_liRemoteVisibilityScale_div_algebraic hT ha
  have hHSupper : ∀ᶠ i in l,
      liRemoteVisibilityScale (a i) (T i) /
          liRemoteAlgebraicVisibilityScale (a i) (T i) < 2 :=
    (tendsto_order.1 hHSratio).2 2 (by norm_num)
  have hH := tendsto_liRemoteVisibilityScale_atTop hT ha
  have hHgt : ∀ᶠ i in l, 1 < liRemoteVisibilityScale (a i) (T i) :=
    hH.eventually_gt_atTop 1
  have hS := tendsto_liRemoteAlgebraicVisibilityScale_atTop hT ha
  have hSgt : ∀ᶠ i in l, 2 ≤ liRemoteAlgebraicVisibilityScale (a i) (T i) :=
    (hS.eventually_gt_atTop 2).mono fun _ hi => hi.le
  filter_upwards [hnupper, hHSupper, hHgt, hSgt] with i hni hHSi hHi hSi
  let H := liRemoteVisibilityScale (a i) (T i)
  let S := liRemoteAlgebraicVisibilityScale (a i) (T i)
  have hHpos : 0 < H := by dsimp [H]; linarith
  have hSpos : 0 < S := by dsimp [S]; linarith
  have hlogHpos : 0 < Real.log H := Real.log_pos (by dsimp [H]; exact hHi)
  have hden : 0 < H * Real.log H := mul_pos hHpos hlogHpos
  have hn : (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) <
      5 * (H * Real.log H) := by
    apply (div_lt_iff₀ hden).mp
    simpa [H] using hni
  have hHS : H < 2 * S := by
    apply (div_lt_iff₀ hSpos).mp
    simpa [H, S] using hHSi
  have hlogHS : Real.log H ≤ Real.log (2 * S) :=
    Real.log_le_log hHpos hHS.le
  have hlogTwo : Real.log 2 ≤ Real.log S :=
    Real.log_le_log (by norm_num) hSi
  have hlogBound : Real.log H ≤ 2 * Real.log S := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hSpos)] at hlogHS
    linarith
  have hlogSnonneg : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  have hmul : H * Real.log H ≤ (2 * S) * (2 * Real.log S) := by
    calc
      H * Real.log H ≤ H * (2 * Real.log S) :=
        mul_le_mul_of_nonneg_left hlogBound hHpos.le
      _ ≤ (2 * S) * (2 * Real.log S) :=
        mul_le_mul_of_nonneg_right hHS.le (by positivity)
  calc
    (liRemoteLogPhaseAlignedDegree (a i) (T i) : ℝ) <
        5 * (H * Real.log H) := hn
    _ ≤ 20 * (S * Real.log S) := by nlinarith

/-- Final quantitative sign-flip theorem: every sufficiently remote quartet in the explicit
same-field carrier has a negative Li coefficient by degree
`20 (T²/a) log(T²/a)`. -/
theorem eventually_exists_liRemoteQuartetGaugedCarrierCoefficient_neg
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    ∀ᶠ i in l, ∃ n : ℕ,
      liRemoteQuartetGaugedCarrierCoefficient alpha n (a i) (T i) < 0 ∧
        (n : ℝ) < 20 * (liRemoteAlgebraicVisibilityScale (a i) (T i) *
          Real.log (liRemoteAlgebraicVisibilityScale (a i) (T i))) := by
  filter_upwards [eventually_liRemoteLogPhaseAlignedGaugedCarrierCoefficient_neg
      halpha hT ha,
    eventually_liRemoteLogPhaseAlignedDegree_lt_algebraicLog hT ha] with i hneg hdegree
  exact ⟨liRemoteLogPhaseAlignedDegree (a i) (T i), hneg, hdegree⟩


end
end RHTower
