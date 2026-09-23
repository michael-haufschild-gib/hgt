import GaloisForLFunctions.RHTower.LiRemoteQuartetProfile
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeMehlerHeine

/-!
# Remote Li quartet coordinate asymptotics

This module proves the card's uniform two-scale law for arbitrary filters: if heights tend to
infinity and the horizontal displacement remains in `(0, 1/2)`, then

`ell * T² / a → 1`, `theta * T → 1`, and `ell / theta → 0`.

It also defines convergence modulo `2π` and proves the universal cosh--cos limit for degrees on
the transverse scale.  No fixed-displacement or sequential specialization is used.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Bounded over divergent is null, over an arbitrary source filter. -/
theorem tendsto_bounded_div_atTop_filter {ι : Type*} {l : Filter ι}
    {f g : ι → ℝ} {K : ℝ} (hg : Tendsto g l atTop)
    (hf : ∀ᶠ i in l, |f i| ≤ K) :
    Tendsto (fun i => f i / g i) l (nhds 0) := by
  have hmaj : Tendsto (fun i => K / g i) l (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hg
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hg.eventually_gt_atTop 0, hf] with i hgi hfi
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hgi]
  exact div_le_div_of_nonneg_right hfi hgi.le

/-- `log (1+u)` has slope one at the origin. -/
theorem tendsto_log_one_add_slope_zero :
    Tendsto (fun u : ℝ => Real.log (1 + u) / u)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
  have hinner : HasDerivAt (fun u : ℝ => u + 1) 1 0 :=
    (hasDerivAt_id 0).add_const 1
  have hderiv : HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
    simpa [add_comm] using hinner.log (by norm_num : (0 : ℝ) + 1 ≠ 0)
  have hslope := hasDerivAt_iff_tendsto_slope.1 hderiv
  refine hslope.congr fun u => ?_
  rw [slope_def_field]
  simp

/-- Small logarithmic-radius parameter in the remote Li coordinate. -/
def liRemoteRadialSmallParameter (a T : ℝ) : ℝ :=
  2 * a / (T ^ (2 : ℕ) + (1 / 2 - a) ^ (2 : ℕ))

/-- The radial coordinate is half of `log (1 + x)` in the small parameter. -/
theorem liRemoteRadialCoordinate_eq_smallParameter (a T : ℝ) :
    liRemoteRadialCoordinate a T =
      (1 / 2 : ℝ) * Real.log (1 + liRemoteRadialSmallParameter a T) := by
  rfl

private theorem halfLogScale_factorization {a d t L : ℝ}
    (ha : a ≠ 0) (hd : d ≠ 0) :
    (1 / 2 : ℝ) * L * t / a = (L / (2 * a / d)) * (t / d) := by
  field_simp [ha, hd]

/-- Exact factorization separating logarithmic slope from denominator geometry. -/
theorem liRemoteRadialScale_factorization {a T : ℝ} (ha : a ≠ 0)
    (hden : T ^ (2 : ℕ) + (1 / 2 - a) ^ (2 : ℕ) ≠ 0) :
    liRemoteRadialCoordinate a T * T ^ (2 : ℕ) / a =
      (Real.log (1 + liRemoteRadialSmallParameter a T) /
          liRemoteRadialSmallParameter a T) *
        (T ^ (2 : ℕ) / (T ^ (2 : ℕ) + (1 / 2 - a) ^ (2 : ℕ))) := by
  rw [liRemoteRadialCoordinate_eq_smallParameter]
  simpa only [liRemoteRadialSmallParameter] using
    (halfLogScale_factorization (a := a)
      (d := T ^ (2 : ℕ) + (1 / 2 - a) ^ (2 : ℕ)) (t := T ^ (2 : ℕ))
      (L := Real.log (1 + liRemoteRadialSmallParameter a T)) ha hden)

/-- Uniform radial asymptotic `ell T² / a → 1`. -/
theorem tendsto_liRemoteRadialScale
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteRadialCoordinate (a i) (T i) * T i ^ (2 : ℕ) / a i)
      l (nhds 1) := by
  have hTpos : ∀ᶠ i in l, 0 < T i := hT.eventually_gt_atTop 0
  have hT2 : Tendsto (fun i => T i ^ (2 : ℕ)) l atTop := by
    refine tendsto_atTop_mono' l ?_ hT
    filter_upwards [hT.eventually_gt_atTop 1] with i hTi
    nlinarith [sq_nonneg (T i - 1)]
  have hb : ∀ᶠ i in l, |(1 / 2 - a i) ^ (2 : ℕ)| ≤ (1 / 4 : ℝ) := by
    filter_upwards [ha] with i hi
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (1 / 2 - a i)]
  have hbdiv : Tendsto (fun i => (1 / 2 - a i) ^ (2 : ℕ) / T i ^ (2 : ℕ)) l (nhds 0) :=
    tendsto_bounded_div_atTop_filter hT2 hb
  have hdenRatio : Tendsto
      (fun i => (T i ^ (2 : ℕ) + (1 / 2 - a i) ^ (2 : ℕ)) / T i ^ (2 : ℕ)) l (nhds 1) := by
    have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
    have h := hone.add hbdiv
    have h' : Tendsto
        (fun i => (T i ^ (2 : ℕ) + (1 / 2 - a i) ^ (2 : ℕ)) / T i ^ (2 : ℕ))
        l (nhds (1 + 0)) := h.congr' (by
          filter_upwards [hTpos] with i hTi
          field_simp [ne_of_gt hTi])
    simpa only [add_zero] using h'
  have hden : Tendsto (fun i => T i ^ (2 : ℕ) + (1 / 2 - a i) ^ (2 : ℕ)) l atTop := by
    refine tendsto_atTop_mono' l ?_ hT2
    filter_upwards with i
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hnumBound : ∀ᶠ i in l, |2 * a i| ≤ (1 : ℝ) := by
    filter_upwards [ha] with i hi
    rw [abs_of_pos (by nlinarith : 0 < 2 * a i)]
    linarith
  have hx : Tendsto (fun i => liRemoteRadialSmallParameter (a i) (T i))
      l (nhds 0) := by
    simpa only [liRemoteRadialSmallParameter] using
      (tendsto_bounded_div_atTop_filter hden hnumBound)
  have hxne : ∀ᶠ i in l, liRemoteRadialSmallParameter (a i) (T i) ≠ 0 := by
    filter_upwards [ha, hTpos] with i hai hTi
    unfold liRemoteRadialSmallParameter
    exact div_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hai.1))
      (by positivity)
  have hxWithin : Tendsto (fun i => liRemoteRadialSmallParameter (a i) (T i))
      l (nhdsWithin 0 ({0}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, hxne⟩
  have hlogSlope := tendsto_log_one_add_slope_zero.comp hxWithin
  have hT2divDen : Tendsto
      (fun i => T i ^ (2 : ℕ) / (T i ^ (2 : ℕ) + (1 / 2 - a i) ^ (2 : ℕ))) l (nhds 1) := by
    have hinv := hdenRatio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [inv_div, inv_one] using hinv
  have hprod := hlogSlope.mul hT2divDen
  have hprod' : Tendsto
      (fun i => liRemoteRadialCoordinate (a i) (T i) * T i ^ (2 : ℕ) / a i)
      l (nhds (1 * 1)) := hprod.congr' (by
        filter_upwards [ha, hTpos] with i hai hTi
        rw [Function.comp_apply]
        exact (liRemoteRadialScale_factorization
          (ne_of_gt hai.1) (by positivity)).symm)
  simpa using hprod'

/-- Small angular parameter in the remote Li coordinate. -/
def liRemoteAngularSmallParameter (a T : ℝ) : ℝ :=
  T / (T ^ (2 : ℕ) - 1 / 4 + a ^ (2 : ℕ))

/-- Principal angular coordinate from card equation (4). -/
def liRemoteAngularCoordinate (a T : ℝ) : ℝ :=
  Real.arctan (liRemoteAngularSmallParameter a T)

/-- The principal angular coordinate is positive above height `1/2`. -/
theorem liRemoteAngularCoordinate_pos {a T : ℝ} (hT : 1 / 2 < T) :
    0 < liRemoteAngularCoordinate a T := by
  have hden : 0 < T ^ (2 : ℕ) - 1 / 4 + a ^ (2 : ℕ) := by
    nlinarith [sq_nonneg a, sq_pos_of_pos (by linarith : 0 < T)]
  unfold liRemoteAngularCoordinate liRemoteAngularSmallParameter
  exact Real.arctan_pos.2 (div_pos (by linarith) hden)

private theorem liRemoteAngularScale_factorization {a T : ℝ}
    (hr : liRemoteAngularSmallParameter a T ≠ 0) :
    liRemoteAngularCoordinate a T * T =
      (Real.arctan (liRemoteAngularSmallParameter a T) /
          liRemoteAngularSmallParameter a T) *
        (liRemoteAngularSmallParameter a T * T) := by
  unfold liRemoteAngularCoordinate
  field_simp [hr]

/-- Uniform angular asymptotic `theta T → 1`. -/
theorem tendsto_liRemoteAngularScale
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteAngularCoordinate (a i) (T i) * T i)
      l (nhds 1) := by
  have hTpos : ∀ᶠ i in l, 1 / 2 < T i := hT.eventually_gt_atTop (1 / 2)
  have hT2 : Tendsto (fun i => T i ^ (2 : ℕ)) l atTop := by
    refine tendsto_atTop_mono' l ?_ hT
    filter_upwards [hT.eventually_gt_atTop 1] with i hTi
    nlinarith [sq_nonneg (T i - 1)]
  have hb : ∀ᶠ i in l, |a i ^ (2 : ℕ) - 1 / 4| ≤ (1 / 4 : ℝ) := by
    filter_upwards [ha] with i hi
    rw [abs_of_nonpos]
    · nlinarith [sq_nonneg (a i)]
    · nlinarith [sq_nonneg (a i), sq_nonneg (1 / 2 - a i)]
  have hbdiv : Tendsto (fun i => (a i ^ (2 : ℕ) - 1 / 4) / T i ^ (2 : ℕ))
      l (nhds 0) := tendsto_bounded_div_atTop_filter hT2 hb
  have hdenRatio : Tendsto
      (fun i => (T i ^ (2 : ℕ) - 1 / 4 + a i ^ (2 : ℕ)) / T i ^ (2 : ℕ))
      l (nhds 1) := by
    have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
    have h := hone.add hbdiv
    have h' : Tendsto
        (fun i => (T i ^ (2 : ℕ) - 1 / 4 + a i ^ (2 : ℕ)) / T i ^ (2 : ℕ))
        l (nhds (1 + 0)) := h.congr' (by
          filter_upwards [hTpos] with i hTi
          field_simp [ne_of_gt (by linarith : 0 < T i)]
          ring)
    simpa only [add_zero] using h'
  have hsmallMul : Tendsto
      (fun i => liRemoteAngularSmallParameter (a i) (T i) * T i)
      l (nhds 1) := by
    have hinv := hdenRatio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hinv' : Tendsto
        (fun i => T i ^ (2 : ℕ) / (T i ^ (2 : ℕ) - 1 / 4 + a i ^ (2 : ℕ)))
        l (nhds 1) := by
      simpa only [inv_div, inv_one] using hinv
    refine hinv'.congr' ?_
    filter_upwards [hTpos] with i hTi
    unfold liRemoteAngularSmallParameter
    have hden : T i ^ (2 : ℕ) - 1 / 4 + a i ^ (2 : ℕ) ≠ 0 := by
      nlinarith [sq_nonneg (a i), sq_pos_of_pos (by linarith : 0 < T i)]
    field_simp [hden]
  have hinvT : Tendsto (fun i => (1 : ℝ) / T i) l (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hT
  have hsmall : Tendsto (fun i => liRemoteAngularSmallParameter (a i) (T i))
      l (nhds 0) := by
    have h := hsmallMul.mul hinvT
    have h' : Tendsto (fun i => liRemoteAngularSmallParameter (a i) (T i))
        l (nhds (1 * 0)) := h.congr' (by
          filter_upwards [hTpos] with i hTi
          field_simp [ne_of_gt (by linarith : 0 < T i)])
    simpa only [mul_zero] using h'
  have hsmallNe : ∀ᶠ i in l,
      liRemoteAngularSmallParameter (a i) (T i) ≠ 0 := by
    filter_upwards [hTpos] with i hTi
    unfold liRemoteAngularSmallParameter
    exact div_ne_zero (ne_of_gt (by linarith : 0 < T i))
      (by nlinarith [sq_nonneg (a i),
        sq_pos_of_pos (by linarith : 0 < T i)])
  have hsmallWithin : Tendsto
      (fun i => liRemoteAngularSmallParameter (a i) (T i))
      l (nhdsWithin 0 ({0}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hsmall, hsmallNe⟩
  have hslope := tendsto_arctan_slope_zero.comp hsmallWithin
  have hprod := hslope.mul hsmallMul
  have hprod' : Tendsto
      (fun i => liRemoteAngularCoordinate (a i) (T i) * T i)
      l (nhds (1 * 1)) := hprod.congr' (by
        filter_upwards [hsmallNe] with i hi
        rw [Function.comp_apply]
        exact (liRemoteAngularScale_factorization hi).symm)
  simpa using hprod'

/-- The transverse radial coordinate is negligible relative to the angular clock. -/
theorem tendsto_liRemoteRadial_div_angular
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i =>
        liRemoteRadialCoordinate (a i) (T i) /
          liRemoteAngularCoordinate (a i) (T i)) l (nhds 0) := by
  have hrad := tendsto_liRemoteRadialScale hT ha
  have hang := tendsto_liRemoteAngularScale hT ha
  have hratio := hrad.div hang (by norm_num : (1 : ℝ) ≠ 0)
  have habound : ∀ᶠ i in l, |a i| ≤ (1 / 2 : ℝ) := by
    filter_upwards [ha] with i hi
    rw [abs_of_pos hi.1]
    exact hi.2.le
  have haDivT : Tendsto (fun i => a i / T i) l (nhds 0) :=
    tendsto_bounded_div_atTop_filter hT habound
  have hprod := hratio.mul haDivT
  have hTpos : ∀ᶠ i in l, 1 / 2 < T i := hT.eventually_gt_atTop (1 / 2)
  have hprod' : Tendsto (fun i =>
      liRemoteRadialCoordinate (a i) (T i) /
        liRemoteAngularCoordinate (a i) (T i)) l (nhds (1 / 1 * 0)) :=
    hprod.congr' (by
      filter_upwards [ha, hTpos] with i hai hTi
      have ha0 : a i ≠ 0 := ne_of_gt hai.1
      have hT0 : T i ≠ 0 := ne_of_gt (by linarith : 0 < T i)
      have htheta0 : liRemoteAngularCoordinate (a i) (T i) ≠ 0 :=
        ne_of_gt (liRemoteAngularCoordinate_pos hTi)
      simp only [Pi.div_apply]
      field_simp [ha0, hT0, htheta0])
  simpa using hprod'

/-- Card equation (5), uniformly for arbitrary cofinal height families and varying displacements
inside `(0, 1/2)`. -/
theorem liRemoteQuartet_coordinate_asymptotics
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2) :
    Tendsto (fun i => liRemoteRadialCoordinate (a i) (T i) * T i ^ (2 : ℕ) / a i)
        l (nhds 1) ∧
      Tendsto (fun i => liRemoteAngularCoordinate (a i) (T i) * T i)
        l (nhds 1) ∧
      Tendsto (fun i => liRemoteRadialCoordinate (a i) (T i) /
        liRemoteAngularCoordinate (a i) (T i)) l (nhds 0) := by
  exact ⟨tendsto_liRemoteRadialScale hT ha,
    tendsto_liRemoteAngularScale hT ha,
    tendsto_liRemoteRadial_div_angular hT ha⟩

/-- Convergence of a real phase modulo integral multiples of `2π`. -/
def TendstoModuloTwoPi {ι : Type*} (phase : ι → ℝ) (l : Filter ι) (phi : ℝ) : Prop :=
  ∃ k : ι → ℤ,
    Tendsto (fun i => phase i - (k i : ℝ) * (2 * Real.pi)) l (nhds phi)

/-- Modulo-`2π` convergence implies convergence of the cosine. -/
theorem TendstoModuloTwoPi.cos {ι : Type*} {phase : ι → ℝ}
    {l : Filter ι} {phi : ℝ} (h : TendstoModuloTwoPi phase l phi) :
    Tendsto (fun i => Real.cos (phase i)) l (nhds (Real.cos phi)) := by
  rcases h with ⟨k, hk⟩
  have hcos := (Real.continuous_cos.tendsto phi).comp hk
  refine hcos.congr fun i => ?_
  simp only [Function.comp_apply]
  have hsplit : phase i =
      (phase i - (k i : ℝ) * (2 * Real.pi)) + (k i : ℝ) * (2 * Real.pi) := by
    ring
  calc
    Real.cos (phase i - (k i : ℝ) * (2 * Real.pi)) =
        Real.cos ((phase i - (k i : ℝ) * (2 * Real.pi)) +
          (k i : ℝ) * (2 * Real.pi)) :=
      (Real.cos_add_int_mul_two_pi _ (k i)).symm
    _ = Real.cos (phase i) := by rw [← hsplit]

/-- Degree scaling `na/T² → c` transports to `n ell → c`. -/
theorem tendsto_liRemoteRadialDegreeScale
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {n : ι → ℕ} {c : ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2)
    (hn : Tendsto (fun i => (n i : ℝ) * a i / T i ^ (2 : ℕ)) l (nhds c)) :
    Tendsto (fun i => (n i : ℝ) * liRemoteRadialCoordinate (a i) (T i))
      l (nhds c) := by
  have hrad := tendsto_liRemoteRadialScale hT ha
  have hprod := hn.mul hrad
  have hTpos : ∀ᶠ i in l, 0 < T i := hT.eventually_gt_atTop 0
  have hprod' : Tendsto
      (fun i => (n i : ℝ) * liRemoteRadialCoordinate (a i) (T i))
      l (nhds (c * 1)) := hprod.congr' (by
        filter_upwards [ha, hTpos] with i hai hTi
        have ha0 : a i ≠ 0 := ne_of_gt hai.1
        have hT0 : T i ≠ 0 := ne_of_gt hTi
        field_simp [ha0, hT0])
  simpa using hprod'

/-- Card equations (27)--(28): universal critical two-scale profile. -/
theorem tendsto_liRemoteQuartetProfile
    {ι : Type*} {l : Filter ι} {a T : ι → ℝ} {n : ι → ℕ} {c phi : ℝ}
    (hT : Tendsto T l atTop)
    (ha : ∀ᶠ i in l, 0 < a i ∧ a i < 1 / 2)
    (hn : Tendsto (fun i => (n i : ℝ) * a i / T i ^ (2 : ℕ)) l (nhds c))
    (hphase : TendstoModuloTwoPi
      (fun i => (n i : ℝ) * liRemoteAngularCoordinate (a i) (T i)) l phi) :
    Tendsto (fun i => liRemoteQuartetProfile (n i)
        (liRemoteRadialCoordinate (a i) (T i))
        (liRemoteAngularCoordinate (a i) (T i)))
      l (nhds (4 * (1 - Real.cosh c * Real.cos phi))) := by
  have hnell := tendsto_liRemoteRadialDegreeScale hT ha hn
  have hcosh := (Real.continuous_cosh.tendsto c).comp hnell
  have hcos := hphase.cos
  have hmul := hcosh.mul hcos
  have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hprofile := (hone.sub hmul).const_mul (4 : ℝ)
  simpa only [liRemoteQuartetProfile, Function.comp_apply] using hprofile

end


end RHTower
