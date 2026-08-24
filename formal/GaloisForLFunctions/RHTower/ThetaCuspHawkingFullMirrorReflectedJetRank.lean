import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorEikonalOrderEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxSourceWeld

/-!
# Infinite reflected-jet rank of full theta-mirror scattering

Exact Davies--Fulling theta-mirror amplitude contains eikonal
`exp (-i t k_a(x))`. Its positive coupling jets contain every source power
`k_a(x)^n`, not only Xi-valued Born term. For reflected pair `k_a, k_{-a}`, define

`Delta_{a,n}(x) = k_a(x)^(n+1) - k_{-a}(x)^(n+1)`.

This module proves exact rank classification: all jets vanish at `a = 0`; at every nonzero
tilt, whole reflected family is real-linearly independent. On positive time ray,
`k_{-a}(x) = k_a(x) exp (-2 a x)`. Superexponential theta decay makes every higher order
asymptotically subordinate to lowest surviving order in any finite relation.

Result strengthens existing second-jet Cayley no-go. Noncentral full mirror carries infinitely
many independent reflected source directions, so actual nonlinear scattering cannot close in a
fixed finite-dimensional two-mode Cayley sector. This does not prove RH: surviving producer
must either propagate infinite tower faithfully through EKG/Teukolsky dynamics or derive a
theta-specific law forbidding a dark infinite-rank reflected sector.
-/


open Complex Real Set Filter Topology

noncomputable section

namespace RHTower

private theorem cancel_common_ratio
    (X Y N D : ℝ) (hY : Y ≠ 0) (hD : D ≠ 0) :
    X * (N / D) = (X * Y) * N / (Y * D) := by
  field_simp [hY, hD]

/-- Order-`n+1` reflected source profile in exact full theta-mirror coupling expansion. -/
def thetaCuspHawkingReflectedFullMirrorJetProfile
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspTiltedSource a x ^ (n + 1) -
    thetaCuspTiltedSource (-a) x ^ (n + 1)

private theorem tendsto_thetaCuspTiltedSource_atTop_zero
    (a : ℝ) :
    Tendsto (thetaCuspTiltedSource a) atTop (𝓝 0) := by
  let C := thetaCuspTiltDecayConstant (a + 1)
  have hneg : Tendsto (fun x : ℝ => -x) atTop atBot := by
    exact tendsto_neg_atBot_iff.mpr tendsto_id
  have hexp : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp hneg
  have hmajor : Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp :
      Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (𝓝 (C * 0)))
  apply squeeze_zero' (g := fun x : ℝ => C * Real.exp (-x))
  · exact Filter.Eventually.of_forall fun x =>
      (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [thetaCuspTiltedSource]
    have hsource := thetaCuspFullSource_le_tiltDecayConstant (a + 1) x
    rw [abs_of_nonneg hx] at hsource
    calc
      Real.exp (a * x) * thetaCuspFullSource x ≤
          Real.exp (a * x) *
            (C * Real.exp (-((a + 1) * x))) :=
        mul_le_mul_of_nonneg_left hsource (Real.exp_pos _).le
      _ = C * Real.exp (-x) := by
        dsimp [C]
        rw [show Real.exp (a * x) *
            (thetaCuspTiltDecayConstant (a + 1) *
              Real.exp (-((a + 1) * x))) =
            thetaCuspTiltDecayConstant (a + 1) *
              (Real.exp (a * x) * Real.exp (-((a + 1) * x))) by ring]
        rw [← Real.exp_add]
        ring_nf
  · exact hmajor

private theorem tendsto_thetaCuspReflectionRatio_atTop_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (-2 * a * x)) atTop (𝓝 0) := by
  have hmul : Tendsto (fun x : ℝ => (2 * a) * x) atTop atTop := by
    exact (tendsto_const_mul_atTop_of_pos (by positivity)).2 tendsto_id
  have hneg : Tendsto (fun x : ℝ => -2 * a * x) atTop atBot := by
    convert tendsto_neg_atBot_iff.mpr hmul using 1
    funext x
    ring
  exact Real.tendsto_exp_atBot.comp hneg

private theorem thetaCuspTiltedSource_neg_eq
    (a x : ℝ) :
    thetaCuspTiltedSource (-a) x =
      thetaCuspTiltedSource a x * Real.exp (-2 * a * x) := by
  unfold thetaCuspTiltedSource
  rw [show Real.exp (a * x) * thetaCuspFullSource x *
      Real.exp (-2 * a * x) =
      (Real.exp (a * x) * Real.exp (-2 * a * x)) *
        thetaCuspFullSource x by ring]
  rw [← Real.exp_add]
  congr 1
  ring

private theorem thetaCuspHawkingReflectedFullMirrorJetProfile_eq_factor
    (a : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspHawkingReflectedFullMirrorJetProfile a n x =
      thetaCuspTiltedSource a x ^ (n + 1) *
        (1 - Real.exp (-2 * a * x) ^ (n + 1)) := by
  rw [thetaCuspHawkingReflectedFullMirrorJetProfile, thetaCuspTiltedSource_neg_eq, mul_pow]
  ring

private theorem reflectedFullMirrorJetProfile_ratio_tendsto_atTop_zero
    {a : ℝ} (ha : 0 < a) {i j : ℕ} (hij : i < j) :
    Tendsto (fun x : ℝ => thetaCuspHawkingReflectedFullMirrorJetProfile a j x / thetaCuspHawkingReflectedFullMirrorJetProfile a i x)
      atTop (𝓝 0) := by
  let A : ℝ → ℝ := thetaCuspTiltedSource a
  let r : ℝ → ℝ := fun x => Real.exp (-2 * a * x)
  have hA : Tendsto A atTop (𝓝 0) :=
    tendsto_thetaCuspTiltedSource_atTop_zero a
  have hr : Tendsto r atTop (𝓝 0) :=
    tendsto_thetaCuspReflectionRatio_atTop_zero ha
  have hji : 0 < j - i := Nat.sub_pos_of_lt hij
  have hApow : Tendsto (fun x => A x ^ (j - i)) atTop (𝓝 0) := by
    convert hA.pow (j - i) using 1
    simp [zero_pow hji.ne']
  have hnum : Tendsto (fun x => 1 - r x ^ (j + 1)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub (hr.pow (j + 1)) using 1
    all_goals simp
  have hden : Tendsto (fun x => 1 - r x ^ (i + 1)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub (hr.pow (i + 1)) using 1
    all_goals simp
  have hquot : Tendsto
      (fun x => (1 - r x ^ (j + 1)) / (1 - r x ^ (i + 1)))
      atTop (𝓝 1) := by
    change Tendsto
      ((fun x => 1 - r x ^ (j + 1)) /
        (fun x => 1 - r x ^ (i + 1))) atTop (𝓝 1)
    convert hnum.div hden (by norm_num) using 1
    all_goals norm_num
  have hnormalized : Tendsto
      (fun x => A x ^ (j - i) *
        ((1 - r x ^ (j + 1)) / (1 - r x ^ (i + 1))))
      atTop (𝓝 0) := by
    convert hApow.mul hquot using 1
    all_goals norm_num
  apply hnormalized.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hAne : A x ≠ 0 := by
    dsimp [A]
    exact (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)).ne'
  have hrlt : r x < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hrnonneg : 0 ≤ r x := (Real.exp_pos _).le
  have hrpowlt : r x ^ (i + 1) < 1 := by
    exact pow_lt_one₀ hrnonneg hrlt (by omega)
  have hdenne : 1 - r x ^ (i + 1) ≠ 0 := by linarith
  rw [thetaCuspHawkingReflectedFullMirrorJetProfile_eq_factor, thetaCuspHawkingReflectedFullMirrorJetProfile_eq_factor]
  dsimp only [A, r]
  have hpow :
      thetaCuspTiltedSource a x ^ (j + 1) =
        thetaCuspTiltedSource a x ^ (j - i) *
          thetaCuspTiltedSource a x ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  have hApowne : thetaCuspTiltedSource a x ^ (i + 1) ≠ 0 :=
    pow_ne_zero _ hAne
  convert cancel_common_ratio
      (thetaCuspTiltedSource a x ^ (j - i))
      (thetaCuspTiltedSource a x ^ (i + 1))
      (1 - Real.exp (-2 * a * x) ^ (j + 1))
      (1 - Real.exp (-2 * a * x) ^ (i + 1))
      hApowne hdenne using 1

private theorem linearIndependent_of_asymptotic_ratio
    {P : Type*} (l : Filter P) [l.NeBot] (w : ℕ → P → ℝ)
    (hne : ∀ i : ℕ, ∀ᶠ p in l, w i p ≠ 0)
    (hratio : ∀ {i j : ℕ}, i < j →
      Tendsto (fun p => w j p / w i p) l (𝓝 0)) :
    LinearIndependent ℝ w := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
      intro c hrelation i hi
      have hs : s.Nonempty := ⟨i, hi⟩
      let i₀ := s.min' hs
      have hi₀ : i₀ ∈ s := Finset.min'_mem s hs
      have hterm : ∀ j ∈ s,
          Tendsto (fun p => c j * (w j p / w i₀ p)) l
            (𝓝 (if j = i₀ then c i₀ else 0)) := by
        intro j hj
        by_cases hji₀ : j = i₀
        · subst j
          apply tendsto_const_nhds.congr'
          filter_upwards [hne i₀] with p hp
          simp [hp]
        · have hi₀j : i₀ < j :=
            lt_of_le_of_ne (Finset.min'_le s j hj) (Ne.symm hji₀)
          simpa [hji₀] using tendsto_const_nhds.mul (hratio hi₀j)
      have hsumLimit :
          Tendsto (fun p => ∑ j ∈ s, c j * (w j p / w i₀ p))
            l (𝓝 (c i₀)) := by
        have hsum := tendsto_finsetSum s hterm
        have htarget :
            (∑ j ∈ s, if j = i₀ then c i₀ else 0) = c i₀ := by
          rw [Finset.sum_eq_single i₀]
          · simp
          · intro j _ hji
            simp [hji]
          · exact fun hnot => (hnot hi₀).elim
        simpa only [htarget] using hsum
      have hzeroEventually :
          ∀ᶠ p in l, ∑ j ∈ s, c j * (w j p / w i₀ p) = 0 := by
        filter_upwards [hne i₀] with p hp
        have hpRelation := congrFun hrelation p
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hpRelation
        calc
          (∑ j ∈ s, c j * (w j p / w i₀ p)) =
              (∑ j ∈ s, c j * w j p) / w i₀ p := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = 0 := by rw [hpRelation, zero_div]
      have hzeroLimit :
          Tendsto (fun p => ∑ j ∈ s, c j * (w j p / w i₀ p))
            l (𝓝 0) :=
        tendsto_const_nhds.congr'
          (hzeroEventually.mono fun _ hp => hp.symm)
      have hci₀ : c i₀ = 0 :=
        tendsto_nhds_unique hsumLimit hzeroLimit
      by_cases hii₀ : i = i₀
      · simpa [hii₀] using hci₀
      · have hrelationErase :
            ∑ j ∈ s.erase i₀, c j • w j = 0 := by
          have hsplit := Finset.add_sum_erase s
            (fun j => c j • w j) hi₀
          rw [hci₀, zero_smul, zero_add] at hsplit
          rw [hsplit, hrelation]
        exact ih (s.erase i₀) (Finset.erase_ssubset hi₀)
          c hrelationErase i (Finset.mem_erase.mpr ⟨hii₀, hi⟩)

private theorem reflectedFullMirrorJetProfile_eventually_ne_zero
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, thetaCuspHawkingReflectedFullMirrorJetProfile a n x ≠ 0 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [thetaCuspHawkingReflectedFullMirrorJetProfile_eq_factor]
  have hsource : 0 < thetaCuspTiltedSource a x :=
    mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
  have hrlt : Real.exp (-2 * a * x) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hrpowlt : Real.exp (-2 * a * x) ^ (n + 1) < 1 :=
    pow_lt_one₀ (Real.exp_pos _).le hrlt (by omega)
  exact mul_ne_zero (pow_ne_zero _ hsource.ne') (by linarith)

private theorem reflectedFullMirrorJetProfile_linearIndependent_of_pos
    {a : ℝ} (ha : 0 < a) :
    LinearIndependent ℝ (fun n : ℕ => thetaCuspHawkingReflectedFullMirrorJetProfile a n) := by
  apply linearIndependent_of_asymptotic_ratio atTop
  · exact reflectedFullMirrorJetProfile_eventually_ne_zero ha
  · intro i j hij
    exact reflectedFullMirrorJetProfile_ratio_tendsto_atTop_zero ha hij

@[simp] theorem thetaCuspHawkingReflectedFullMirrorJetProfile_zero_tilt
    (n : ℕ) :
    thetaCuspHawkingReflectedFullMirrorJetProfile 0 n = 0 := by
  funext x
  simp [thetaCuspHawkingReflectedFullMirrorJetProfile]

/-- Reversing modular tilt reverses every reflected nonlinear source jet. -/
theorem thetaCuspHawkingReflectedFullMirrorJetProfile_neg_tilt (a : ℝ) (n : ℕ) :
    thetaCuspHawkingReflectedFullMirrorJetProfile (-a) n =
      -thetaCuspHawkingReflectedFullMirrorJetProfile a n := by
  funext x
  change thetaCuspHawkingReflectedFullMirrorJetProfile (-a) n x =
    -thetaCuspHawkingReflectedFullMirrorJetProfile a n x
  unfold thetaCuspHawkingReflectedFullMirrorJetProfile
  simp only [neg_neg]
  ring

/-- **Infinite reflected nonlinear rank.** Every noncentral theta-mirror tilt supplies a
real-linearly independent source direction at every positive coupling order. -/
theorem thetaCuspHawkingReflectedFullMirrorJetProfile_linearIndependent
    {a : ℝ} (ha : a ≠ 0) :
    LinearIndependent ℝ (fun n : ℕ => thetaCuspHawkingReflectedFullMirrorJetProfile a n) := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hpos : 0 < -a := neg_pos.mpr haNeg
    have hlinear := reflectedFullMirrorJetProfile_linearIndependent_of_pos hpos
    rw [linearIndependent_iff'] at hlinear ⊢
    intro s c hrelation i hi
    apply hlinear s c
    · funext x
      have hx := congrFun hrelation x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hx ⊢
      calc
        (∑ j ∈ s, c j * thetaCuspHawkingReflectedFullMirrorJetProfile (-a) j x) =
            ∑ j ∈ s, -(c j * thetaCuspHawkingReflectedFullMirrorJetProfile a j x) := by
          apply Finset.sum_congr rfl
          intro j _
          have hjx := congrFun
            (thetaCuspHawkingReflectedFullMirrorJetProfile_neg_tilt a j) x
          change thetaCuspHawkingReflectedFullMirrorJetProfile (-a) j x =
            -thetaCuspHawkingReflectedFullMirrorJetProfile a j x at hjx
          rw [hjx]
          ring
        _ = -(∑ j ∈ s, c j * thetaCuspHawkingReflectedFullMirrorJetProfile a j x) := by simp
        _ = 0 := by rw [hx, neg_zero]
    · exact hi
  · exact reflectedFullMirrorJetProfile_linearIndependent_of_pos haPos

/-- Exact collapse/rank dichotomy for full reflected theta-mirror jet tower. -/
theorem thetaCuspHawkingReflectedFullMirrorJetProfile_linearIndependent_iff
    (a : ℝ) :
    LinearIndependent ℝ
        (fun n : ℕ => thetaCuspHawkingReflectedFullMirrorJetProfile a n) ↔
      a ≠ 0 := by
  constructor
  · intro hlinear ha
    subst a
    exact (hlinear.ne_zero 0)
      (thetaCuspHawkingReflectedFullMirrorJetProfile_zero_tilt 0)
  · exact thetaCuspHawkingReflectedFullMirrorJetProfile_linearIndependent

end RHTower
